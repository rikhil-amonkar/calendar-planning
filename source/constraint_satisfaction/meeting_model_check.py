import json
import os
from datetime import datetime
from typing import Dict, List, Tuple, Union, Optional

# =============================================
# CONFIGURATION - SET YOUR FILE PATHS HERE
# =============================================

LLM_RESPONSE_FILE = "meeting_planning/100_random_0shot_text_outputs_new/O3-M-25-01-31_forceJSON_text_meeting_results.json"
CONSTRAINTS_FOLDER = "constraint_satisfaction/meeting"
OUTPUT_FILE = "constraint_satisfaction/calendar_constraint_satisfaction_results/text_satisfaction/meeting_text/O3-M-25-01-31_meeting_satisfaction.txt"

# =============================================
# END OF CONFIGURATION
# =============================================

def parse_time(time_str: str) -> Optional[float]:
    """Convert time string to float hours, handling leading zeros and None values"""
    if time_str is None:
        return None
    try:
        # Handle times with leading zeros (e.g., "09:30" becomes "9:30")
        if time_str.startswith('0') and ':' in time_str:
            time_str = time_str[1:] if time_str[1] != ':' else '0' + time_str[2:]
        
        dt = datetime.strptime(time_str, "%H:%M")
        return dt.hour + dt.minute / 60
    except ValueError:
        if ':' in time_str:
            hours, minutes = time_str.split(':')
            # Remove leading zeros from hours
            hours = hours.lstrip('0') or '0'
            return float(hours) + float(minutes) / 60
        return float(time_str)

def time_to_float(time_data: Dict[str, str]) -> Tuple[Optional[float], Optional[float]]:
    """Convert time dict to float tuple"""
    try:
        start = parse_time(time_data.get('start_time'))
        end = parse_time(time_data.get('end_time'))
        return (start, end)
    except (KeyError, ValueError, AttributeError):
        return (None, None)

def is_valid_meeting(meeting: Dict) -> bool:
    """Check if a meeting dictionary has all required fields"""
    required = ['action', 'location', 'person', 'start_time', 'end_time']
    return all(key in meeting for key in required)

def is_time_in_range(time_range: Tuple[float, float], constraint_range: Dict) -> bool:
    """Check if time range falls within constraint range"""
    try:
        constraint_start = constraint_range['from'] if isinstance(constraint_range['from'], (int, float)) else parse_time(constraint_range['from'])
        constraint_end = constraint_range['to'] if isinstance(constraint_range['to'], (int, float)) else parse_time(constraint_range['to'])
        
        start, end = time_range
        if start is None or end is None:
            return False
            
        return start >= constraint_start and end <= constraint_end
    except (KeyError, ValueError):
        return False

def count_constraints(constraints: Dict) -> Dict[str, int]:
    """Count constraints in all categories"""
    counts = {
        'location_constraints': 0,
        'person_availability': 0,
        'duration_requirements': 0,
        'travel_times': 0
    }
    
    if 'constraints' in constraints:
        for constraint in constraints['constraints']:
            if 'location' in constraint and 'time_of_day' in constraint:
                counts['location_constraints'] += 1
            if 'person' in constraint and 'duration' in constraint:
                counts['person_availability'] += 1
                if 'min_meeting_duration' in constraint:
                    counts['duration_requirements'] += 1
    
    if 'travel_distances' in constraints:
        counts['travel_times'] = len(constraints['travel_distances'])
    
    return counts

def check_meeting_duration(meeting: Dict, person: str, min_duration: float) -> bool:
    """Check if meeting meets minimum duration requirement"""
    try:
        start, end = time_to_float(meeting)
        if start is None or end is None:
            return False
        duration = end - start
        return duration >= min_duration and meeting['person'] == person
    except (KeyError, ValueError):
        return False

def check_travel_time(prev_meeting: Dict, current_meeting: Dict, travel_distances: List[Dict]) -> bool:
    """Check if travel time between meetings is sufficient"""
    try:
        if not prev_meeting or not current_meeting:
            return True
            
        prev_end = parse_time(prev_meeting['end_time'])
        current_start = parse_time(current_meeting['start_time'])
        
        if prev_end is None or current_start is None:
            return True
            
        travel_time_needed = None
        for distance in travel_distances:
            if (distance['place']['from'] == prev_meeting['location'] and 
                distance['place']['to'] == current_meeting['location']):
                travel_time_needed = distance['walking_time'] / 60  # convert minutes to hours
                break
        
        if travel_time_needed is None:
            return True  # No travel constraint between these locations
            
        return (current_start - prev_end) >= travel_time_needed
    except (KeyError, ValueError):
        return True

def check_constraints(itinerary: List[Dict], constraints: Dict) -> Tuple[int, int, Dict[str, int], Dict[str, int]]:
    """Check itinerary against all constraints"""
    constraint_counts = count_constraints(constraints)
    total_constraints = sum(constraint_counts.values())
    broken_constraints = 0
    satisfied_by_category = {cat: 0 for cat in constraint_counts.keys()}
    
    # Handle null or empty itinerary
    if not itinerary or itinerary == "None":
        return total_constraints, total_constraints, constraint_counts, satisfied_by_category
    
    # Check location constraints (must be at specific location at specific time)
    for constraint in constraints.get('constraints', []):
        if 'location' in constraint and 'time_of_day' in constraint:
            location = constraint['location']
            required_time = constraint['time_of_day']
            satisfied = False
            
            for meeting in itinerary:
                if meeting['location'] == location:
                    start_time = parse_time(meeting['start_time'])
                    if start_time is not None and abs(start_time - required_time) < 0.25:  # within 15 minutes
                        satisfied = True
                        break
            
            if satisfied:
                satisfied_by_category['location_constraints'] += 1
            else:
                broken_constraints += 1
    
    # Check person availability and duration requirements
    for constraint in constraints.get('constraints', []):
        if 'person' in constraint and 'duration' in constraint:
            person = constraint['person']
            duration_range = constraint['duration']
            min_duration = constraint.get('min_meeting_duration', 0)
            person_satisfied = False
            duration_satisfied = False
            
            for meeting in itinerary:
                if meeting['person'] == person:
                    meeting_range = time_to_float(meeting)
                    if is_time_in_range(meeting_range, duration_range):
                        person_satisfied = True
                        if check_meeting_duration(meeting, person, min_duration):
                            duration_satisfied = True
                            break
            
            if person_satisfied:
                satisfied_by_category['person_availability'] += 1
            else:
                broken_constraints += 1
            
            if 'min_meeting_duration' in constraint:
                if duration_satisfied:
                    satisfied_by_category['duration_requirements'] += 1
                else:
                    broken_constraints += 1
    
    # Check travel times between consecutive meetings
    travel_distances = constraints.get('travel_distances', [])
    for i in range(1, len(itinerary)):
        if not check_travel_time(itinerary[i-1], itinerary[i], travel_distances):
            broken_constraints += 1
        else:
            satisfied_by_category['travel_times'] += 1
    
    return total_constraints, broken_constraints, constraint_counts, satisfied_by_category

def load_constraints(constraints_folder: str) -> Dict[str, Dict]:
    """Load all constraints from folder"""
    constraints = {}
    for filename in os.listdir(constraints_folder):
        if filename.endswith('.json'):
            try:
                with open(os.path.join(constraints_folder, filename), 'r') as f:
                    data = json.load(f)
                    for example_id, constraint_data in data.items():
                        constraints[example_id] = constraint_data
            except (json.JSONDecodeError, IOError) as e:
                print(f"Warning: Could not load {filename}: {str(e)}")
    return constraints

def process_examples(llm_data: Dict, constraints: Dict) -> List[str]:
    """Process all examples"""
    results = []
    for example in llm_data.get('0shot', []):
        example_id = example['count']
        
        if example_id not in constraints:
            results.append(f"{example_id} | ERROR: Constraints not found")
            continue
        
        try:
            model_itinerary = example.get('final_program_time', {}).get('itinerary', [])
            
            # Handle null or empty responses
            if not model_itinerary or model_itinerary == "None":
                total = sum(count_constraints(constraints[example_id]).values())
                results.append(
                    f"{example_id} | Model Response: None | "
                    f"Total Constraints: {total} | "
                    f"Constraints Broken: {total} | "
                    f"Constraints Satisfied: 0 | "
                    f"Response Accuracy: 0.00% | "
                    f"Breakdown: Location: 0/0, Person: 0/0, Duration: 0/0, Travel: 0/0"
                )
                continue
                
            total, broken, counts, satisfied_counts = check_constraints(model_itinerary, constraints[example_id])
            satisfied = total - broken
            accuracy = (satisfied / total * 100) if total > 0 else 100
            
            # Create a summary of the itinerary
            itinerary_summary = "; ".join(
                f"{m['person']}@{m['location']}({m['start_time']}-{m['end_time']})"
                for m in model_itinerary[:3]  # Show first 3 meetings for brevity
            )
            if len(model_itinerary) > 3:
                itinerary_summary += f" ... (+{len(model_itinerary)-3} more)"
                
            breakdown = (
                f"Location: {satisfied_counts['location_constraints']}/{counts['location_constraints']}, "
                f"Person: {satisfied_counts['person_availability']}/{counts['person_availability']}, "
                f"Duration: {satisfied_counts['duration_requirements']}/{counts['duration_requirements']}, "
                f"Travel: {satisfied_counts['travel_times']}/{counts['travel_times']}"
            )
            
            results.append(
                f"{example_id} | Model Response: {itinerary_summary} | "
                f"Total Constraints: {total} | "
                f"Constraints Broken: {broken} | "
                f"Constraints Satisfied: {satisfied} | "
                f"Response Accuracy: {accuracy:.2f}% | "
                f"Breakdown: {breakdown}"
            )
        except Exception as e:
            results.append(f"{example_id} | ERROR: {str(e)}")
    
    return results

def main():
    """Main function"""
    try:
        with open(LLM_RESPONSE_FILE, 'r') as f:
            llm_data = json.load(f)
    except Exception as e:
        print(f"Error loading LLM data: {str(e)}")
        return
    
    if not os.path.exists(CONSTRAINTS_FOLDER):
        print(f"Constraints folder not found: {CONSTRAINTS_FOLDER}")
        return
    
    constraints = load_constraints(CONSTRAINTS_FOLDER)
    if not constraints:
        print("No valid constraints loaded")
        return
    
    results = process_examples(llm_data, constraints)
    
    try:
        with open(OUTPUT_FILE, 'w') as f:
            f.write("\n".join(results))
        print(f"Results written to {OUTPUT_FILE}")
    except Exception as e:
        print(f"Error writing results: {str(e)}")

if __name__ == "__main__":
    main()


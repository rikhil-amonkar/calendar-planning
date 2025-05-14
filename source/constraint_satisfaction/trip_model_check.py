import json
import os
from typing import Dict, List, Tuple, Union

# =============================================
# CONFIGURATION - SET YOUR FILE PATHS HERE
# =============================================

LLM_RESPONSE_FILE = "trip_planning/100_random_0shot_code_outputs/O3-M-25-01-31_code_trip_results.json"
CONSTRAINTS_FOLDER = "constraint_satisfaction/trip"
OUTPUT_FILE = "constraint_satisfaction/calendar_constraint_satisfaction_results/code_satisfaction/trip_code/O3-M-25-01-31_trip_satisfaction.txt"

# =============================================
# END OF CONFIGURATION
# =============================================

def parse_day_range(day_range: Union[str, Dict]) -> Tuple[int, int]:
    """Convert day range string to start and end days"""
    if day_range is None or day_range == "None":
        return (None, None)
    
    try:
        if isinstance(day_range, dict):
            day_range_str = day_range.get('day_range', '')
        else:
            day_range_str = str(day_range)
        
        if day_range_str.startswith("Day "):
            day_range_str = day_range_str[4:]
        parts = day_range_str.split('-')
        start = int(parts[0].strip())
        end = int(parts[1].strip()) if len(parts) > 1 else start
        return (start, end)
    except (ValueError, IndexError, AttributeError):
        return (None, None)

def is_valid_itinerary_item(item: Union[Dict, str]) -> bool:
    """Check if an itinerary item has all required fields"""
    if isinstance(item, str):
        return False
    return 'day_range' in item and 'place' in item and item['place'] and item['day_range']

def count_constraints(constraints: Dict) -> Dict[str, int]:
    """Count constraints in all categories"""
    counts = {
        'city_length': len(constraints.get('city_length', [])),
        'city_day_ranges': len(constraints.get('city_day_ranges', [])),
        'direct_flights': len(constraints.get('direct_flights', []))
    }
    return counts

def check_city_days(itinerary: List[Union[Dict, str]], constraints: Dict) -> Tuple[int, int]:
    """Check if cities have correct number of days"""
    if not itinerary:
        return (0, len(constraints.get('city_length', [])))
    
    city_days = {}
    for item in itinerary:
        if not is_valid_itinerary_item(item):
            continue
        start, end = parse_day_range(item['day_range'])
        if start is None or end is None:
            continue
        city = item['place']
        city_days[city] = city_days.get(city, 0) + (end - start + 1)
    
    broken = 0
    for constraint in constraints.get('city_length', []):
        city = constraint['city']
        expected_days = constraint['days']
        actual_days = city_days.get(city, 0)
        if actual_days != expected_days:
            broken += 1
    
    return (len(constraints.get('city_length', [])), broken)

def check_city_ranges(itinerary: List[Union[Dict, str]], constraints: Dict) -> Tuple[int, int]:
    """Check if cities are in correct day ranges"""
    if not itinerary:
        return (0, len(constraints.get('city_day_ranges', [])))
    
    broken = 0
    for constraint in constraints.get('city_day_ranges', []):
        city = constraint['city']
        expected_start = constraint['start']
        expected_end = constraint['end']
        
        found = False
        for item in itinerary:
            if not is_valid_itinerary_item(item) or item['place'] != city:
                continue
            start, end = parse_day_range(item['day_range'])
            if start is None or end is None:
                continue
            if start == expected_start and end == expected_end:
                found = True
                break
        
        if not found:
            broken += 1
    
    return (len(constraints.get('city_day_ranges', [])), broken)

def check_flight_connections(itinerary: List[Union[Dict, str]], constraints: Dict) -> Tuple[int, int]:
    """Check if flight connections follow direct flight rules"""
    if not itinerary or len(itinerary) < 2:
        return (0, len(constraints.get('direct_flights', [])))
    
    direct_flights = constraints.get('direct_flights', [])
    flight_pairs = [(f['from'], f['to']) for f in direct_flights]
    
    broken = 0
    for i in range(len(itinerary)-1):
        current = itinerary[i]
        next_item = itinerary[i+1]
        
        if not is_valid_itinerary_item(current) or not is_valid_itinerary_item(next_item):
            continue
            
        from_city = current['place']
        to_city = next_item['place']
        
        if from_city == to_city:
            continue  # Same city, no flight needed
            
        if (from_city, to_city) not in flight_pairs:
            broken += 1
    
    return (len(direct_flights), broken)

def check_trip_length(itinerary: List[Union[Dict, str]], constraints: Dict) -> Tuple[int, int]:
    """Check if total trip length matches constraint"""
    if not itinerary:
        return (1, 1)  # Count as broken if no itinerary
    
    last_day = 0
    for item in itinerary:
        if not is_valid_itinerary_item(item):
            continue
        start, end = parse_day_range(item['day_range'])
        if start is None or end is None:
            continue
        if end > last_day:
            last_day = end
    
    expected_length = constraints.get('trip_length', 0)
    broken = 1 if last_day != expected_length else 0
    return (1, broken)

def check_constraints(model_itinerary: Union[Dict, str, None], constraints: Dict) -> Tuple[int, int, Dict[str, int], Dict[str, int]]:
    """Check all trip planning constraints"""
    constraint_counts = count_constraints(constraints)
    total_constraints = sum(constraint_counts.values()) + 1  # +1 for trip length
    broken_constraints = 0
    satisfied_by_category = {
        'city_length': 0,
        'city_day_ranges': 0,
        'direct_flights': 0,
        'trip_length': 0
    }
    
    # Handle null or "None" responses
    if model_itinerary is None or model_itinerary == "None":
        return (total_constraints, total_constraints, constraint_counts, satisfied_by_category)
    
    try:
        # Handle case where model_itinerary might be a string
        if isinstance(model_itinerary, str):
            try:
                model_itinerary = json.loads(model_itinerary)
            except json.JSONDecodeError:
                return (total_constraints, total_constraints, constraint_counts, satisfied_by_category)
        
        itinerary = model_itinerary.get('itinerary', []) if isinstance(model_itinerary, dict) else []
        if not itinerary:
            return (total_constraints, total_constraints, constraint_counts, satisfied_by_category)
    except Exception:
        return (total_constraints, total_constraints, constraint_counts, satisfied_by_category)
    
    # Check each type of constraint
    total_city_days, broken_city_days = check_city_days(itinerary, constraints)
    satisfied_by_category['city_length'] = total_city_days - broken_city_days
    broken_constraints += broken_city_days
    
    total_city_ranges, broken_city_ranges = check_city_ranges(itinerary, constraints)
    satisfied_by_category['city_day_ranges'] = total_city_ranges - broken_city_ranges
    broken_constraints += broken_city_ranges
    
    total_flights, broken_flights = check_flight_connections(itinerary, constraints)
    satisfied_by_category['direct_flights'] = total_flights - broken_flights
    broken_constraints += broken_flights
    
    total_length, broken_length = check_trip_length(itinerary, constraints)
    satisfied_by_category['trip_length'] = total_length - broken_length
    broken_constraints += broken_length
    
    return (total_constraints, broken_constraints, constraint_counts, satisfied_by_category)

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
            model_itinerary = example.get('final_program_time', {})
            
            # Handle case where itinerary might be a string or list
            if isinstance(model_itinerary, str):
                try:
                    model_itinerary = json.loads(model_itinerary)
                except json.JSONDecodeError:
                    model_itinerary = {"itinerary": []}
            elif isinstance(model_itinerary, list):
                model_itinerary = {"itinerary": model_itinerary}
            
            # Handle null or "None" responses explicitly
            if (model_itinerary is None or model_itinerary == "None" or 
                not model_itinerary.get('itinerary') or 
                (isinstance(model_itinerary.get('itinerary'), list) and 
                 len(model_itinerary['itinerary']) == 1 and 
                 model_itinerary['itinerary'][0] in [None, "None"])):
                total = sum(count_constraints(constraints[example_id]).values()) + 1  # +1 for trip length
                results.append(
                    f"{example_id} | Model Response: None | "
                    f"Total Constraints: {total} | "
                    f"Constraints Broken: {total} | "
                    f"Constraints Satisfied: 0 | "
                    f"Response Accuracy: 0.00% | "
                    f"Breakdown: City Days: 0/0, City Ranges: 0/0, Flights: 0/0, Trip Length: 0/1"
                )
                continue
                
            total, broken, counts, satisfied_counts = check_constraints(model_itinerary, constraints[example_id])
            satisfied = total - broken
            accuracy = (satisfied / total * 100) if total > 0 else 100
            
            # Create a summary of the itinerary
            itinerary_items = model_itinerary.get('itinerary', [])
            if isinstance(itinerary_items, str):
                try:
                    itinerary_items = json.loads(itinerary_items)
                except json.JSONDecodeError:
                    itinerary_items = []
            
            itinerary_summary = "; ".join(
                f"{item.get('place', '?')} ({item.get('day_range', '?')})" 
                for item in (itinerary_items[:3] if isinstance(itinerary_items, list) else [])
            )
            if isinstance(itinerary_items, list) and len(itinerary_items) > 3:
                itinerary_summary += " ..."
            
            breakdown = (f"City Days: {satisfied_counts['city_length']}/{counts['city_length']}, "
                       f"City Ranges: {satisfied_counts['city_day_ranges']}/{counts['city_day_ranges']}, "
                       f"Flights: {satisfied_counts['direct_flights']}/{counts['direct_flights']}, "
                       f"Trip Length: {satisfied_counts['trip_length']}/1")
            
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
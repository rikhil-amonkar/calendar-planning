import json
import os
from typing import Dict, List, Tuple, Union

# Configuration - Set your file paths here
RESPONSES_FILE = "calendar_scheduling/100_random_0shot_text_outputs_new/O3-M-25-01-31_forceJSON_text_calendar_results.json"
CONSTRAINTS_DIR = "constraint_satisfaction/calendar/"
JSON_OUTPUT_FILE = "constraint_satisfaction/calendar_constraint_satisfaction_results/text_satisfaction/calendar_text/evaluation_results.json"
TEXT_OUTPUT_FILE = "constraint_satisfaction/calendar_constraint_satisfaction_results/text_satisfaction/calendar_text/evaluation_results.txt"

def load_model_responses(response_file_path: str) -> Dict[str, Dict]:
    """Load model responses from JSON file and index them by example_id."""
    with open(response_file_path, 'r') as f:
        data = json.load(f)
    
    responses = {}
    for category in data.values():  # e.g., "0shot", "1shot", etc.
        for response in category:
            example_id = response['count']
            responses[example_id] = response
    return responses

def load_constraint_dicts(constraints_dir: str) -> Dict[str, Dict]:
    """Load all constraint dictionaries from a directory and index by example_id."""
    constraint_dicts = {}
    for filename in os.listdir(constraints_dir):
        if filename.endswith('.json'):
            filepath = os.path.join(constraints_dir, filename)
            with open(filepath, 'r') as f:
                data = json.load(f)
                for example_id, constraints in data.items():
                    constraint_dicts[example_id] = constraints
    return constraint_dicts

def time_to_decimal(time_str: str) -> float:
    """Convert time string (HH:MM) to decimal hours (e.g., '14:30' -> 14.5)."""
    hours, minutes = map(int, time_str.split(':'))
    return hours + minutes / 60.0

def parse_model_time(model_response: Dict) -> Tuple[str, float, float]:
    """Extract day and time range from model response."""
    day = model_response['final_program_time']['day']
    start_time = time_to_decimal(model_response['final_program_time']['start_time'])
    end_time = time_to_decimal(model_response['final_program_time']['end_time'])
    return day, start_time, end_time

def ranges_overlap(range1: Tuple[float, float], range2: Tuple[float, float]) -> bool:
    """Check if two time ranges overlap."""
    return not (range1[1] <= range2[0] or range2[1] <= range1[0])

def check_constraints(
    model_day: str, 
    model_start: float, 
    model_end: float, 
    constraints: Dict[str, List[Dict]]
) -> Dict[str, int]:
    """Check model time against all constraints and count violations."""
    results = {
        'allowed_breaks': 0,
        'disallowed_breaks': 0,
        'preferred_breaks': 0,
        'unpreferred_breaks': 0,
        'total_constraints': 0
    }
    
    model_range = (model_start, model_end)
    
    # Check allowed ranges (should be within at least one allowed range)
    allowed_breaks = 0
    if 'allowed_ranges' in constraints:
        allowed_ranges = constraints['allowed_ranges']
        results['total_constraints'] += len(allowed_ranges)
        
        # Model time must overlap with at least one allowed range
        overlaps_allowed = any(
            (r['day'] == model_day and ranges_overlap(model_range, (r['start'], r['end'])))
            for r in allowed_ranges
        )
        if not overlaps_allowed:
            allowed_breaks = len(allowed_ranges)
    
    results['allowed_breaks'] = allowed_breaks
    
    # Check disallowed ranges (should not overlap with any)
    disallowed_breaks = 0
    if 'disallowed_ranges' in constraints:
        disallowed_ranges = constraints['disallowed_ranges']
        results['total_constraints'] += len(disallowed_ranges)
        
        # Count how many disallowed ranges the model time overlaps with
        disallowed_breaks = sum(
            1 for r in disallowed_ranges
            if r['day'] == model_day and ranges_overlap(model_range, (r['start'], r['end']))
        )
    
    results['disallowed_breaks'] = disallowed_breaks
    
    # Check preferred ranges (should be within at least one preferred range)
    preferred_breaks = 0
    if 'preferred_ranges' in constraints:
        preferred_ranges = constraints['preferred_ranges']
        results['total_constraints'] += len(preferred_ranges)
        
        # Model time must overlap with at least one preferred range
        overlaps_preferred = any(
            (r['day'] == model_day and ranges_overlap(model_range, (r['start'], r['end'])))
            for r in preferred_ranges
        )
        if not overlaps_preferred:
            preferred_breaks = len(preferred_ranges)
    
    results['preferred_breaks'] = preferred_breaks
    
    # Check unpreferred ranges (should not overlap with any)
    unpreferred_breaks = 0
    if 'unpreferred_ranges' in constraints:
        unpreferred_ranges = constraints['unpreferred_ranges']
        results['total_constraints'] += len(unpreferred_ranges)
        
        # Count how many unpreferred ranges the model time overlaps with
        unpreferred_breaks = sum(
            1 for r in unpreferred_ranges
            if r['day'] == model_day and ranges_overlap(model_range, (r['start'], r['end']))
        )
    
    results['unpreferred_breaks'] = unpreferred_breaks
    
    return results

def evaluate_responses(
    model_responses: Dict[str, Dict], 
    constraint_dicts: Dict[str, Dict]
) -> Dict[str, Dict]:
    """Evaluate all model responses against their corresponding constraints."""
    evaluations = {}
    
    for example_id, model_response in model_responses.items():
        if example_id not in constraint_dicts:
            continue  # Skip if no matching constraint dict
            
        constraints = constraint_dicts[example_id]
        
        try:
            day, start, end = parse_model_time(model_response)
            constraint_results = check_constraints(day, start, end, constraints)
            
            total_breaks = (
                constraint_results['allowed_breaks'] +
                constraint_results['disallowed_breaks'] +
                constraint_results['preferred_breaks'] +
                constraint_results['unpreferred_breaks']
            )
            
            total_constraints = constraint_results['total_constraints']
            accuracy = (total_constraints - total_breaks) / total_constraints if total_constraints > 0 else 0
            
            evaluations[example_id] = {
                'constraint_results': constraint_results,
                'total_breaks': total_breaks,
                'total_constraints': total_constraints,
                'accuracy': accuracy,
                'model_time': {
                    'day': day,
                    'start': start,
                    'end': end
                }
            }
        except (KeyError, ValueError) as e:
            print(f"Error processing {example_id}: {str(e)}")
            evaluations[example_id] = {
                'error': str(e)
            }
    
    return evaluations

def save_evaluations(evaluations: Dict[str, Dict], json_output_path: str, text_output_path: str):
    """Save evaluation results to both JSON and text files."""
    # Save JSON output
    with open(json_output_path, 'w') as f:
        json.dump(evaluations, f, indent=2)
    
    # Save text output
    with open(text_output_path, 'w') as f:
        # Write header
        f.write("example_id | Model Response: {start:end}, Day | Total Constraints: total | Constraint Satisfaction: score/total | Response Accuracy: %\n")
        f.write("-" * 120 + "\n")
        
        # Write each evaluation
        for example_id, eval_data in evaluations.items():
            if 'error' in eval_data:
                f.write(f"{example_id} | ERROR: {eval_data['error']}\n")
                continue
            
            model_time = eval_data['model_time']
            total_constraints = eval_data['total_constraints']
            total_breaks = eval_data['total_breaks']
            accuracy_pct = eval_data['accuracy'] * 100
            
            # Format time as HH:MM
            start_str = f"{int(model_time['start'])}:{int((model_time['start'] % 1) * 60):02d}"
            end_str = f"{int(model_time['end'])}:{int((model_time['end'] % 1) * 60):02d}"
            
            line = (
                f"{example_id} | "
                f"Model Response: {{{start_str}:{end_str}}}, {model_time['day']} | "
                f"Total Constraints: {total_constraints} | "
                f"Constraint Satisfaction: {total_constraints - total_breaks}/{total_constraints} | "
                f"Response Accuracy: {accuracy_pct:.2f}%\n"
            )
            f.write(line)

def main():
    print("Loading model responses...")
    model_responses = load_model_responses(RESPONSES_FILE)
    print(f"Loaded {len(model_responses)} model responses.")
    
    print("Loading constraint dictionaries...")
    constraint_dicts = load_constraint_dicts(CONSTRAINTS_DIR)
    print(f"Loaded {len(constraint_dicts)} constraint dictionaries.")
    
    print("Evaluating responses...")
    evaluations = evaluate_responses(model_responses, constraint_dicts)
    
    print("Saving results...")
    save_evaluations(evaluations, JSON_OUTPUT_FILE, TEXT_OUTPUT_FILE)
    
    print(f"Evaluation complete. Results saved to:")
    print(f"- JSON: {JSON_OUTPUT_FILE}")
    print(f"- Text: {TEXT_OUTPUT_FILE}")

if __name__ == '__main__':
    main()


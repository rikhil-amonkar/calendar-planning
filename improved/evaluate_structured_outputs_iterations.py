#!/usr/bin/env python3
"""
Evaluate structured outputs with iterations using the constraint-based evaluator.

This version evaluates the final iteration result (after all iterations) rather than
just the first attempt. It also provides statistics about iterations.

This script works with outputs from convert_to_structured_output_iterations.py
"""

import json
import sys
from pathlib import Path
from typing import Dict, List
from datetime import datetime


def evaluate_meeting(constraints, pred_dict):
    """
    Evaluate meeting plan against constraints.
    Extracted from evaluate_by_constraint.py to avoid dependency issues.
    """
    from datetime import datetime

    def parse_time(s):
        # Return None for invalid time formats instead of raising exception
        try:
            # handles "H:MM" or "H:MMAM"/"H:MMPM"
            if s.endswith(("AM", "PM")):
                return datetime.strptime(s, "%I:%M%p")
            return datetime.strptime(s, "%H:%M")
        except ValueError:
            return None

    # build map person→availability & location
    people = {p["name"]: p for p in constraints.get("people_to_meet", [])}
    start_location = constraints.get("start", {}).get("location")
    start_time = constraints.get("start", {}).get("time_of_day")
    num_people_to_meet = constraints.get("num_people_to_meet", 0)

    # parse predicted meetings
    meetings = []
    for m in pred_dict.get("itinerary", []):
        name = m["person"]
        start = parse_time(m["start_time"])
        end = parse_time(m["end_time"])
        if start is None or end is None:  # Invalid time format
            return False, {"invalid_time_format": {"start": m["start_time"], "end": m["end_time"]}}
        loc = people.get(name, {}).get("location")
        meetings.append({"person": name, "start": start, "end": end, "location": loc})

    if len(meetings) < num_people_to_meet:
        return False, {"num_people_to_meet": num_people_to_meet}
    # sort chronologically
    meetings.sort(key=lambda x: x["start"])

    # 1) each meeting must lie within that person's available window
    for m in meetings:
        p = people.get(m["person"])
        if not p:
            continue
        avail = p["time_of_day"]
        av_from = parse_time(avail["from"])
        av_to = parse_time(avail["to"])
        if m["start"] < av_from or m["end"] > av_to:
            return False, {"person": m["person"], "time_of_day": avail}

    # 2) build travel‐time lookup
    travel = {}
    for d in constraints.get("travel_distances", []):
        pl = d["place"]
        frm = pl.get("from", constraints.get("start", {}).get("location"))
        to = pl["to"]
        travel[(frm, to)] = d["walking_time"]

    # 3) check start‐to‐first meeting
    # parse start time
    if start_time:
        st = parse_time(start_time)
        first = meetings[0]
        # 0a) meeting must not start before you arrive
        if first["start"] < st:
            return False, {"start_time": start_time}
        # 0b) travel from start_location
        walk0 = travel.get((start_location, first["location"]))
        gap0 = (first["start"] - st).total_seconds() / 60
        if walk0 is not None and walk0 > gap0:
            return False, {
                "travel_start": {
                    "to_person": first["person"],
                    "to_location": first["location"],
                    "travel_time": walk0
                }
            }

    # 3) check following meetings
    for a, b in zip(meetings, meetings[1:]):
        gap_mins = (b["start"] - a["end"]).total_seconds() / 60
        walk = travel.get((a["location"], b["location"]))
        if walk is not None and walk > gap_mins:
            return False, {
                "travel": {
                    "from_person": a["person"],
                    "to_person": b["person"],
                    "from_location": a["location"],
                    "to_location": b["location"],
                    "travel_time": walk
                }
            }

    return True, {}


def load_constraints(constraints_file: str) -> Dict:
    """Load constraints from JSON file."""
    with open(constraints_file, 'r') as f:
        return json.load(f)


def evaluate_structured_output_iterations(structured_file: str, constraints_file: str) -> None:
    """
    Evaluate a structured output file with iterations against constraints.
    
    This evaluates the FINAL iteration result (after all iterations), not the first attempt.
    
    Args:
        structured_file: Path to structured output JSON (from convert_to_structured_output_iterations.py)
        constraints_file: Path to constraints JSON
    """
    # Load data
    with open(structured_file, 'r') as f:
        structured_data = json.load(f)
    
    with open(constraints_file, 'r') as f:
        all_constraints = json.load(f)
    
    print(f"✓ Loaded {len(structured_data)} structured outputs (with iterations)")
    print(f"✓ Loaded {len(all_constraints)} constraint sets")
    
    # Evaluate each problem
    results = []
    correct_count = 0
    total_count = len(structured_data)  # Always count all samples
    missing_constraints = []
    
    # Statistics about iterations
    iteration_stats = {
        'total_iterations': 0,
        'problems_with_iterations': 0,
        'problems_successful_on_first': 0,
        'problems_successful_after_retries': 0,
        'problems_failed_all_iterations': 0
    }
    
    for item in structured_data:
        problem_id = item['problem_id']
        
        # Get the final itinerary from iterations data
        # This is the result AFTER all iterations, not the first attempt
        iterations_data = item.get('iterations_data', {})
        itinerary = iterations_data.get('final_itinerary', [])
        
        # Fallback to structured_output if iterations_data not available
        if not itinerary:
            itinerary = item.get('structured_output', {}).get('itinerary', [])
        
        # Track iteration statistics
        num_iterations = iterations_data.get('num_iterations', 0)
        has_successful_iteration = iterations_data.get('has_successful_iteration', False)
        final_iteration_index = iterations_data.get('final_iteration_index')
        
        if num_iterations > 0:
            iteration_stats['total_iterations'] += num_iterations
            iteration_stats['problems_with_iterations'] += 1
            
            # Check if first iteration succeeded
            iterations_list = iterations_data.get('iterations', [])
            if iterations_list and len(iterations_list) > 0:
                first_iter_success = (
                    iterations_list[0].get('execution_success', False) and 
                    iterations_list[0].get('itinerary', [])
                )
                if first_iter_success:
                    iteration_stats['problems_successful_on_first'] += 1
                elif has_successful_iteration:
                    iteration_stats['problems_successful_after_retries'] += 1
                else:
                    iteration_stats['problems_failed_all_iterations'] += 1
        
        # Count samples with no itinerary as incorrect
        if not itinerary:
            results.append({
                'problem_id': problem_id,
                'status': 'no_plan',
                'is_correct': False,
                'violated_constraint': {},
                'num_meetings': 0,
                'execution_success': item.get('execution_success', False),
                'num_iterations': num_iterations,
                'final_iteration_index': final_iteration_index,
                'has_successful_iteration': has_successful_iteration
            })
            continue
        
        # Get constraints for this problem
        if problem_id not in all_constraints:
            missing_constraints.append(problem_id)
            results.append({
                'problem_id': problem_id,
                'status': 'no_constraints',
                'is_correct': False,
                'violated_constraint': {},
                'num_meetings': len(itinerary),
                'execution_success': item.get('execution_success', False),
                'num_iterations': num_iterations,
                'final_iteration_index': final_iteration_index,
                'has_successful_iteration': has_successful_iteration
            })
            continue
        
        constraints = all_constraints[problem_id].get('constraints', {})
        
        # Set num_people_to_meet from the people_to_meet array length
        # This is required for the evaluate_meeting function to properly validate
        # that all required people are met. The JSON structure has people_to_meet
        # as an array, so we derive num_people_to_meet from its length.
        if 'people_to_meet' in constraints and 'num_people_to_meet' not in constraints:
            constraints['num_people_to_meet'] = len(constraints['people_to_meet'])
        
        # Evaluate the FINAL iteration result
        pred_dict = {'itinerary': itinerary}
        is_correct, violated_constraint = evaluate_meeting(constraints, pred_dict)
        
        if is_correct:
            correct_count += 1
        
        results.append({
            'problem_id': problem_id,
            'status': 'correct' if is_correct else 'wrong_plan',
            'is_correct': is_correct,
            'violated_constraint': violated_constraint,
            'num_meetings': len(itinerary),
            'execution_success': item.get('execution_success', False),
            'num_iterations': num_iterations,
            'final_iteration_index': final_iteration_index,
            'has_successful_iteration': has_successful_iteration
        })
        
        # Print violations
        if not is_correct and violated_constraint:
            print(f"\n✗ {problem_id}: {violated_constraint} (after {num_iterations} iterations)")
    
    # Count problems with no plan
    no_plan_count = sum(1 for r in results if r['status'] == 'no_plan')
    
    # Print summary
    print(f"\n{'='*70}")
    print(f"CONSTRAINT-BASED EVALUATION SUMMARY (FINAL ITERATION)")
    print(f"{'='*70}")
    print(f"Total problems:          {total_count}")
    print(f"With extractable plans:  {total_count - no_plan_count}")
    print(f"No plan extracted:       {no_plan_count}")
    print(f"Missing constraints:     {len(missing_constraints)}")
    print(f"Correct (final result):  {correct_count} / {total_count} ({correct_count/total_count*100:.1f}%)")
    print(f"{'='*70}")
    
    # Print iteration statistics
    if iteration_stats['problems_with_iterations'] > 0:
        print(f"\nITERATION STATISTICS:")
        print(f"  Problems with iterations:        {iteration_stats['problems_with_iterations']}")
        print(f"  Total iterations across problems: {iteration_stats['total_iterations']}")
        if iteration_stats['problems_with_iterations'] > 0:
            avg_iterations = iteration_stats['total_iterations'] / iteration_stats['problems_with_iterations']
            print(f"  Average iterations per problem:   {avg_iterations:.2f}")
        print(f"  Successful on first iteration:    {iteration_stats['problems_successful_on_first']}")
        print(f"  Successful after retries:          {iteration_stats['problems_successful_after_retries']}")
        print(f"  Failed all iterations:             {iteration_stats['problems_failed_all_iterations']}")
    
    print(f"{'='*70}\n")
    
    if missing_constraints:
        print(f"Problems missing constraints: {missing_constraints[:5]}...")
    
    # Save results to eval_results folder (one level up from structured_results)
    # If input is in structured_results/, go up one level to improved/, then into eval_results/
    eval_results_dir = Path(structured_file).parent.parent / "eval_results"
    
    # Create directory if it doesn't exist
    eval_results_dir.mkdir(exist_ok=True)
    
    output_path = eval_results_dir / f"{Path(structured_file).stem}_constraint_eval.json"
    with open(output_path, 'w') as f:
        json.dump({
            'summary': {
                'total': total_count,
                'with_plans': total_count - no_plan_count,
                'no_plans': no_plan_count,
                'correct': correct_count,
                'accuracy': correct_count / total_count if total_count > 0 else 0,
                'iteration_stats': iteration_stats
            },
            'results': results
        }, f, indent=2)
    
    print(f"✓ Detailed results saved to: {output_path}")
    
    # Show some examples
    print(f"\nSample CORRECT results (final iteration):")
    correct_examples = [r for r in results if r['is_correct']][:3]
    for ex in correct_examples:
        iter_info = f" ({ex['num_iterations']} iterations)" if ex['num_iterations'] > 0 else ""
        print(f"  ✓ {ex['problem_id']}: {ex['num_meetings']} meetings{iter_info}")
    
    print(f"\nSample INCORRECT results (final iteration):")
    incorrect_examples = [r for r in results if not r['is_correct'] and r['status'] != 'no_plan'][:3]
    for ex in incorrect_examples:
        iter_info = f" ({ex['num_iterations']} iterations)" if ex['num_iterations'] > 0 else ""
        print(f"  ✗ {ex['problem_id']}: {ex['violated_constraint']}{iter_info}")


def main():
    """Main function."""
    if len(sys.argv) < 3:
        print("Usage: python evaluate_structured_outputs_iterations.py <structured_output.json> <constraints.json>")
        print("\nArguments:")
        print("  structured_output.json : Path to structured output file (from convert_to_structured_output_iterations.py)")
        print("  constraints.json       : Path to constraints file (meeting_planning_100_constraints.json)")
        print("\nExample:")
        print("  python evaluate_structured_outputs_iterations.py \\")
        print("    code_generation_results/meeting_test_structured_iterations.json \\")
        print("    meeting_planning_100_constraints.json")
        print("\nNote: This evaluates the FINAL iteration result (after all retries),")
        print("      not just the first attempt. This gives you the accuracy after")
        print("      the model has had multiple chances to fix errors.")
        sys.exit(1)
    
    structured_file = sys.argv[1]
    constraints_file = sys.argv[2]
    
    if not Path(structured_file).exists():
        print(f"Error: File not found: {structured_file}")
        sys.exit(1)
    
    if not Path(constraints_file).exists():
        print(f"Error: File not found: {constraints_file}")
        sys.exit(1)
    
    evaluate_structured_output_iterations(structured_file, constraints_file)
    
    print("\n" + "="*70)
    print("EVALUATION COMPLETE")
    print("="*70)
    print("\nThis evaluation shows accuracy based on the FINAL result after all iterations.")
    print("This means if a model failed on the first attempt but succeeded on a later")
    print("iteration, it counts as correct. This gives you the 'best possible' accuracy")
    print("after allowing the model to refine its solution.")


if __name__ == "__main__":
    main()

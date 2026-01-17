#!/usr/bin/env python3
"""
Evaluate structured outputs using the constraint-based evaluator.

This script adapts our structured outputs to work with evaluate_by_constraint.py's
evaluation functions.
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


def evaluate_structured_output(structured_file: str, constraints_file: str) -> None:
    """
    Evaluate a structured output file against constraints.
    
    Args:
        structured_file: Path to structured output JSON
        constraints_file: Path to constraints JSON
    """
    # Load data
    with open(structured_file, 'r') as f:
        structured_data = json.load(f)
    
    with open(constraints_file, 'r') as f:
        all_constraints = json.load(f)
    
    print(f"✓ Loaded {len(structured_data)} structured outputs")
    print(f"✓ Loaded {len(all_constraints)} constraint sets")
    
    # Evaluate each problem
    results = []
    correct_count = 0
    total_count = len(structured_data)  # Always count all samples
    missing_constraints = []
    
    for item in structured_data:
        problem_id = item['problem_id']
        itinerary = item['structured_output']['itinerary']
        
        # Count samples with no itinerary as incorrect
        if not itinerary:
            results.append({
                'problem_id': problem_id,
                'status': 'no_plan',
                'is_correct': False,
                'violated_constraint': {},
                'num_meetings': 0,
                'execution_success': item.get('execution_success', False)
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
                'execution_success': item.get('execution_success', False)
            })
            continue
        
        constraints = all_constraints[problem_id].get('constraints', {})
        
        # Get the expected number of people to meet from golden solution
        golden_solution = item.get('golden_solution', '')
        if golden_solution:
            # Parse golden solution to count meetings
            try:
                if isinstance(golden_solution, str):
                    golden_list = eval(golden_solution)  # Convert string representation to list
                else:
                    golden_list = golden_solution
                
                # Count meetings in golden solution
                num_people_to_meet = sum(1 for line in golden_list if 'You meet' in line)
                constraints['num_people_to_meet'] = num_people_to_meet
            except:
                pass
        
        # Evaluate
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
            'execution_success': item.get('execution_success', False)
        })
        
        # Print violations
        if not is_correct and violated_constraint:
            print(f"\n✗ {problem_id}: {violated_constraint}")
    
    # Count problems with no plan
    no_plan_count = sum(1 for r in results if r['status'] == 'no_plan')
    
    # Print summary
    print(f"\n{'='*70}")
    print(f"CONSTRAINT-BASED EVALUATION SUMMARY")
    print(f"{'='*70}")
    print(f"Total problems:          {total_count}")
    print(f"With extractable plans:  {total_count - no_plan_count}")
    print(f"No plan extracted:       {no_plan_count}")
    print(f"Missing constraints:     {len(missing_constraints)}")
    print(f"Correct (constraints):   {correct_count} / {total_count} ({correct_count/total_count*100:.1f}%)")
    print(f"{'='*70}\n")
    
    if missing_constraints:
        print(f"Problems missing constraints: {missing_constraints[:5]}...")
    
    # Save results
    output_path = Path(structured_file).parent / f"{Path(structured_file).stem}_constraint_eval.json"
    with open(output_path, 'w') as f:
        json.dump({
            'summary': {
                'total': total_count,
                'with_plans': total_count - no_plan_count,
                'no_plans': no_plan_count,
                'correct': correct_count,
                'accuracy': correct_count / total_count if total_count > 0 else 0
            },
            'results': results
        }, f, indent=2)
    
    print(f"✓ Detailed results saved to: {output_path}")
    
    # Show some examples
    print(f"\nSample CORRECT results:")
    correct_examples = [r for r in results if r['is_correct']][:3]
    for ex in correct_examples:
        print(f"  ✓ {ex['problem_id']}: {ex['num_meetings']} meetings")
    
    print(f"\nSample INCORRECT results:")
    incorrect_examples = [r for r in results if not r['is_correct'] and r['status'] != 'no_plan'][:3]
    for ex in incorrect_examples:
        print(f"  ✗ {ex['problem_id']}: {ex['violated_constraint']}")


def main():
    """Main function."""
    if len(sys.argv) < 3:
        print("Usage: python evaluate_structured_outputs.py <structured_output.json> <constraints.json>")
        print("\nArguments:")
        print("  structured_output.json : Path to structured output file (from convert_to_structured_output.py)")
        print("  constraints.json       : Path to constraints file (meeting_planning_100_constraints.json)")
        print("\nExample:")
        print("  python evaluate_structured_outputs.py \\")
        print("    code_generation_results/meeting_test_Qwen2_5-32B-Instruct_20260111_191941_structured.json \\")
        print("    /path/to/meeting_planning_100_constraints.json")
        sys.exit(1)
    
    structured_file = sys.argv[1]
    constraints_file = sys.argv[2]
    
    if not Path(structured_file).exists():
        print(f"Error: File not found: {structured_file}")
        sys.exit(1)
    
    if not Path(constraints_file).exists():
        print(f"Error: File not found: {constraints_file}")
        sys.exit(1)
    
    evaluate_structured_output(structured_file, constraints_file)
    
    print("\n" + "="*70)
    print("EVALUATION COMPLETE")
    print("="*70)


if __name__ == "__main__":
    main()

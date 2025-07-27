#!/usr/bin/env python3

import json
import sys
import os

# Add the source directory to the path
sys.path.append('source')

from iterative_plan_refinement_parallel import evaluate_meeting, evaluate_calendar, evaluate_trip
from iterative_plan_refinement_parallel_noConstraintFeedback import evaluate_meeting as evaluate_meeting_ncf, evaluate_calendar as evaluate_calendar_ncf, evaluate_trip as evaluate_trip_ncf

def load_constraints(task):
    """Load constraints from the appropriate JSON file - consistent with SMT program"""
    task_name_map = {
        "calendar": "calendar_scheduling",
        "trip": "trip_planning",
        "meeting": "meeting_planning"
    }
    with open(f"data/{task_name_map[task]}_100_constraints.json") as f:
        constraints_data = json.load(f)
        return {example_id: data.get("constraints", {}) for example_id, data in constraints_data.items()}

def test_example_118():
    # Load constraints for example 118
    constraints = load_constraints("meeting")
    example_118_constraints = constraints.get("meeting_planning_example_118", {})
    
    print("Constraints for example 118:")
    print(json.dumps(example_118_constraints, indent=2))
    
    # Model's prediction (from the evaluation.json file)
    pred_dict = {
        "itinerary": [
            {
                "action": "meet",
                "person": "Richard",
                "start_time": "09:15",
                "end_time": "11:15"
            },
            {
                "action": "meet",
                "person": "Charles",
                "start_time": "11:39",
                "end_time": "13:00"
            }
        ]
    }
    
    print("\nModel's prediction:")
    print(json.dumps(pred_dict, indent=2))
    
    # Test the evaluation with both versions
    print("\n=== Testing iterative_plan_refinement_parallel.py ===")
    constraints_satisfied, violated_constraints = evaluate_meeting(example_118_constraints, pred_dict)
    print(f"Constraints satisfied: {constraints_satisfied}")
    print(f"Violated constraints: {violated_constraints}")
    
    print("\n=== Testing iterative_plan_refinement_parallel_noConstraintFeedback.py ===")
    constraints_satisfied_ncf, violated_constraints_ncf = evaluate_meeting_ncf(example_118_constraints, pred_dict)
    print(f"Constraints satisfied: {constraints_satisfied_ncf}")
    print(f"Violated constraints: {violated_constraints_ncf}")
    
    # Check consistency
    print(f"\n=== Consistency Check ===")
    print(f"Results match: {constraints_satisfied == constraints_satisfied_ncf and violated_constraints == violated_constraints_ncf}")
    
    # Analyze the travel time issue
    print("\n=== Travel Time Analysis ===")
    
    # Travel from Bayview to Union Square (Richard)
    bayview_to_union = 17  # minutes
    print(f"Travel time from Bayview to Union Square: {bayview_to_union} minutes")
    print(f"Start time: 9:00AM, Meeting start: 9:15AM")
    print(f"Available time: 15 minutes")
    print(f"Travel time required: {bayview_to_union} minutes")
    print(f"Travel constraint satisfied: {bayview_to_union <= 15}")
    
    # Travel from Union Square to Presidio (Charles)
    union_to_presidio = 24  # minutes
    print(f"\nTravel time from Union Square to Presidio: {union_to_presidio} minutes")
    print(f"First meeting ends: 11:15AM, Second meeting starts: 11:39AM")
    print(f"Available time: 24 minutes")
    print(f"Travel time required: {union_to_presidio} minutes")
    print(f"Travel constraint satisfied: {union_to_presidio <= 24}")

def test_example_131():
    """Test example 131 for meeting duration validation"""
    print("\n" + "="*60)
    print("TESTING EXAMPLE 131 - MEETING DURATION VALIDATION")
    print("="*60)
    
    # Load constraints for example 131
    constraints = load_constraints("meeting")
    example_131_constraints = constraints.get("meeting_planning_example_131", {})
    
    print("Constraints for example 131:")
    print(json.dumps(example_131_constraints, indent=2))
    
    # Model's prediction (from the evaluation.json file)
    pred_dict = {
        "itinerary": [
            {
                "action": "meet",
                "person": "Jason",
                "start_time": "10:00",
                "end_time": "16:15"
            },
            {
                "action": "meet",
                "person": "Kenneth",
                "start_time": "16:25",
                "end_time": "16:45"
            }
        ]
    }
    
    print("\nModel's prediction:")
    print(json.dumps(pred_dict, indent=2))
    
    # Test the evaluation with both versions
    print("\n=== Testing iterative_plan_refinement_parallel.py ===")
    constraints_satisfied, violated_constraints = evaluate_meeting(example_131_constraints, pred_dict)
    print(f"Constraints satisfied: {constraints_satisfied}")
    print(f"Violated constraints: {violated_constraints}")
    
    print("\n=== Testing iterative_plan_refinement_parallel_noConstraintFeedback.py ===")
    constraints_satisfied_ncf, violated_constraints_ncf = evaluate_meeting_ncf(example_131_constraints, pred_dict)
    print(f"Constraints satisfied: {constraints_satisfied_ncf}")
    print(f"Violated constraints: {violated_constraints_ncf}")
    
    # Analyze the meeting duration issue
    print("\n=== Meeting Duration Analysis ===")
    
    # Jason's meeting
    jason_start = "10:00"
    jason_end = "16:15"
    jason_required = 90  # minutes
    jason_actual = (16 * 60 + 15) - (10 * 60)  # 375 minutes
    print(f"Jason meeting: {jason_start} to {jason_end}")
    print(f"Required: {jason_required} minutes, Actual: {jason_actual} minutes")
    print(f"Duration constraint satisfied: {jason_actual >= jason_required}")
    
    # Kenneth's meeting
    kenneth_start = "16:25"
    kenneth_end = "16:45"
    kenneth_required = 45  # minutes
    kenneth_actual = (16 * 60 + 45) - (16 * 60 + 25)  # 20 minutes
    print(f"\nKenneth meeting: {kenneth_start} to {kenneth_end}")
    print(f"Required: {kenneth_required} minutes, Actual: {kenneth_actual} minutes")
    print(f"Duration constraint satisfied: {kenneth_actual >= kenneth_required}")
    
    print(f"\nExpected result: Constraints should NOT be satisfied due to Kenneth's short meeting duration")

def test_consistency():
    """Test that all evaluation methods are consistent"""
    print("\n" + "="*60)
    print("CONSISTENCY TESTING")
    print("="*60)
    
    # Test with a simple calendar example
    calendar_constraints = {
        "meeting_duration": 1.0,
        "disallowed_ranges": []
    }
    
    calendar_pred = {
        "day": "Monday",
        "start_time": "10:00",
        "end_time": "11:00"
    }
    
    print("\nTesting Calendar Evaluation Consistency:")
    result1 = evaluate_calendar(calendar_constraints, calendar_pred)
    result2 = evaluate_calendar_ncf(calendar_constraints, calendar_pred)
    print(f"iterative_plan_refinement_parallel.py: {result1}")
    print(f"iterative_plan_refinement_parallel_noConstraintFeedback.py: {result2}")
    print(f"Consistent: {result1 == result2}")
    
    # Test with a simple trip example
    trip_constraints = {
        "trip_length": 3,
        "city_length": [{"city": "Paris", "days": 2}, {"city": "London", "days": 1}],
        "direct_flights": [{"from": "Paris", "to": "London"}]
    }
    
    trip_pred = {
        "itinerary": [
            {"day_range": "Day 1-2", "place": "Paris"},
            {"day_range": "Day 3-3", "place": "London"}
        ]
    }
    
    print("\nTesting Trip Evaluation Consistency:")
    result1 = evaluate_trip(trip_constraints, trip_pred)
    result2 = evaluate_trip_ncf(trip_constraints, trip_pred)
    print(f"iterative_plan_refinement_parallel.py: {result1}")
    print(f"iterative_plan_refinement_parallel_noConstraintFeedback.py: {result2}")
    print(f"Consistent: {result1 == result2}")

def compare_evaluation_methods():
    """Compare the evaluation methods between the two files"""
    print("\n" + "="*60)
    print("COMPARISON OF EVALUATION METHODS")
    print("="*60)
    
    print("\n1. MEETING EVALUATION DIFFERENCES:")
    print("- iterative_plan_refinement_parallel.py (OLD):")
    print("  * Only checked if people were met (num_people_to_meet or people_to_meet)")
    print("  * Did NOT check travel times between locations")
    print("  * Did NOT check if meetings fit within availability windows")
    print("  * Did NOT check meeting durations")
    
    print("\n- iterative_smt_refinement_enhanced.py (CORRECT):")
    print("  * Checks travel times between all consecutive meetings")
    print("  * Checks if meetings fit within each person's availability window")
    print("  * Checks travel time from start location to first meeting")
    print("  * Validates time formats and chronological order")
    
    print("\n2. CALENDAR EVALUATION DIFFERENCES:")
    print("- iterative_plan_refinement_parallel.py:")
    print("  * Uses 'time_range' field in format 'HH:MM:HH:MM'")
    print("  * Has default meeting duration fallback of 1.0")
    
    print("\n- iterative_smt_refinement_enhanced.py:")
    print("  * Uses 'start_time' and 'end_time' fields")
    print("  * Requires meeting_duration to be specified in constraints")
    print("  * More robust time parsing")
    
    print("\n3. TRIP EVALUATION DIFFERENCES:")
    print("- Both files have similar trip evaluation logic")
    print("- Both check trip length, stay durations, and flight connectivity")
    print("- iterative_smt_refinement_enhanced.py has additional event range checking")

if __name__ == "__main__":
    test_example_118()
    test_example_131()
    test_consistency()
    compare_evaluation_methods() 
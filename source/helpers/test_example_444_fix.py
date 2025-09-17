#!/usr/bin/env python3

import sys
import os
import json

sys.path.append('.')
from iterative_plan_refinement_parallel import load_constraints, evaluate_meeting

def test_example_444():
    print("=== Testing Example 444 Fix ===")
    
    # Load constraints
    constraints = load_constraints("meeting")
    example_id = "meeting_planning_example_444"
    
    if example_id not in constraints:
        print(f"✗ Example {example_id} not found in constraints")
        return
    
    example_constraints = constraints[example_id]
    print(f"Example: {example_id}")
    print(f"Number of people_to_meet: {len(example_constraints.get('people_to_meet', []))}")
    print(f"People to meet: {[p['name'] for p in example_constraints.get('people_to_meet', [])]}")
    
    # Test prediction that meets 4 people (same as gold)
    test_pred = {
        "itinerary": [
            {"action": "meet", "person": "Patricia", "start_time": "09:31", "end_time": "10:31"},
            {"action": "meet", "person": "Laura", "start_time": "12:30", "end_time": "12:45"},
            {"action": "meet", "person": "Mary", "start_time": "15:00", "end_time": "16:00"},
            {"action": "meet", "person": "Emily", "start_time": "16:15", "end_time": "17:15"}
        ]
    }
    
    # Test without num_people_to_meet (old behavior)
    print("\n--- Testing without num_people_to_meet (old behavior) ---")
    result_old, violations_old = evaluate_meeting(example_constraints, test_pred)
    print(f"Result: {result_old}")
    print(f"Violations: {violations_old}")
    
    # Test with num_people_to_meet = 4 (new behavior)
    print("\n--- Testing with num_people_to_meet = 4 (new behavior) ---")
    example_constraints_with_num = example_constraints.copy()
    example_constraints_with_num["num_people_to_meet"] = 4
    result_new, violations_new = evaluate_meeting(example_constraints_with_num, test_pred)
    print(f"Result: {result_new}")
    print(f"Violations: {violations_new}")
    
    # Test with num_people_to_meet = 5 (should fail)
    print("\n--- Testing with num_people_to_meet = 5 (should fail) ---")
    example_constraints_with_num["num_people_to_meet"] = 5
    result_fail, violations_fail = evaluate_meeting(example_constraints_with_num, test_pred)
    print(f"Result: {result_fail}")
    print(f"Violations: {violations_fail}")
    
    print("\n=== Summary ===")
    print(f"Old behavior (without num_people_to_meet): {'FAIL' if not result_old else 'PASS'}")
    print(f"New behavior (with num_people_to_meet = 4): {'FAIL' if not result_new else 'PASS'}")
    print(f"Expected failure (with num_people_to_meet = 5): {'PASS' if not result_fail else 'FAIL'}")
    
    if result_new and not result_old:
        print("✅ Fix works correctly!")
    else:
        print("❌ Fix does not work as expected")

if __name__ == "__main__":
    test_example_444() 
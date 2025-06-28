#!/usr/bin/env python3

import sys
import os
import json

sys.path.append('.')
from iterative_plan_refinement_parallel import load_constraints, evaluate_calendar, evaluate_trip, evaluate_meeting

def test_calendar_constraints():
    print("=== Testing Calendar Constraints (Plan Program) ===")
    constraints = load_constraints("calendar")
    example_id = "calendar_scheduling_example_1"
    if example_id in constraints:
        example_constraints = constraints[example_id]
        print(f"Example: {example_id}")
        print(f"Constraints keys: {list(example_constraints.keys())}")
        print(f"Meeting duration: {example_constraints.get('meeting_duration')}")
        print(f"Number of disallowed ranges: {len(example_constraints.get('disallowed_ranges', []))}")
        print(f"First disallowed range: {example_constraints.get('disallowed_ranges', [])[0] if example_constraints.get('disallowed_ranges') else 'None'}")
        print()
        # Test evaluation function
        test_pred = {"day": "Monday", "time_range": "{09:30:10:00}"}
        result, violations = evaluate_calendar(example_constraints, test_pred)
        print(f"Evaluation result: {result}")
        print(f"Violations: {violations}")
        return example_constraints
    else:
        print(f"✗ Example {example_id} not found in constraints")
        return None

def test_trip_constraints():
    print("=== Testing Trip Constraints (Plan Program) ===")
    constraints = load_constraints("trip")
    example_id = "trip_planning_example_142"
    if example_id in constraints:
        example_constraints = constraints[example_id]
        print(f"Example: {example_id}")
        print(f"Constraints keys: {list(example_constraints.keys())}")
        print(f"Trip length: {example_constraints.get('trip_length')}")
        print(f"Number of city_length entries: {len(example_constraints.get('city_length', []))}")
        print(f"First city_length entry: {example_constraints.get('city_length', [])[0] if example_constraints.get('city_length') else 'None'}")
        print()
        # Test evaluation function
        test_pred = {"itinerary": [
            {"day_range": "Day 1-4", "place": "Madrid"},
            {"day_range": "Day 4-6", "place": "Dublin"},
            {"day_range": "Day 6-7", "place": "Tallinn"}
        ]}
        result, violations = evaluate_trip(example_constraints, test_pred)
        print(f"Evaluation result: {result}")
        print(f"Violations: {violations}")
        return example_constraints
    else:
        print(f"✗ Example {example_id} not found in constraints")
        return None

def test_meeting_constraints():
    print("=== Testing Meeting Constraints (Plan Program) ===")
    constraints = load_constraints("meeting")
    example_id = "meeting_planning_example_131"
    if example_id in constraints:
        example_constraints = constraints[example_id]
        print(f"Example: {example_id}")
        print(f"Constraints keys: {list(example_constraints.keys())}")
        print(f"Number of people_to_meet: {len(example_constraints.get('people_to_meet', []))}")
        print(f"First person: {example_constraints.get('people_to_meet', [])[0] if example_constraints.get('people_to_meet') else 'None'}")
        print()
        # Test evaluation function
        test_pred = {"itinerary": [
            {"person": "Jason", "start_time": "10:00", "end_time": "11:30"}
        ]}
        result, violations = evaluate_meeting(example_constraints, test_pred)
        print(f"Evaluation result: {result}")
        print(f"Violations: {violations}")
        return example_constraints
    else:
        print(f"✗ Example {example_id} not found in constraints")
        return None

def main():
    print("Testing Plan Program Constraints Extraction and Evaluation")
    print("=" * 50)
    calendar_constraints = test_calendar_constraints()
    trip_constraints = test_trip_constraints()
    meeting_constraints = test_meeting_constraints()
    print("\n" + "=" * 50)
    print("Test Summary:")
    if calendar_constraints and 'meeting_duration' in calendar_constraints:
        print("✓ Calendar constraints: PASSED")
    else:
        print("✗ Calendar constraints: FAILED")
    if trip_constraints and 'trip_length' in trip_constraints:
        print("✓ Trip constraints: PASSED")
    else:
        print("✗ Trip constraints: FAILED")
    if meeting_constraints and 'people_to_meet' in meeting_constraints:
        print("✓ Meeting constraints: PASSED")
    else:
        print("✗ Meeting constraints: FAILED")

if __name__ == "__main__":
    main() 
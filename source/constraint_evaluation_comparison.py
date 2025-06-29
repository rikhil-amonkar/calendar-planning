#!/usr/bin/env python3

import sys
import os
import json

sys.path.append('.')
from iterative_plan_refinement_parallel import evaluate_calendar as plan_evaluate_calendar
from iterative_plan_refinement_parallel import evaluate_meeting as plan_evaluate_meeting
from iterative_plan_refinement_parallel import evaluate_trip as plan_evaluate_trip
from iterative_smt_refinement import evaluate_calendar as smt_evaluate_calendar
from iterative_smt_refinement import evaluate_meeting as smt_evaluate_meeting
from iterative_smt_refinement import evaluate_trip as smt_evaluate_trip

def compare_calendar_evaluation():
    print("=== Calendar Evaluation Comparison ===")
    
    # Test cases for calendar
    test_cases = [
        {
            "name": "Valid calendar",
            "constraints": {
                "meeting_duration": 1.0,
                "disallowed_ranges": [{"day": "Monday", "start": 10.0, "end": 11.0}]
            },
            "pred": {"day": "Tuesday", "start_time": "14:30", "end_time": "15:30"}
        },
        {
            "name": "Invalid duration",
            "constraints": {
                "meeting_duration": 1.0,
                "disallowed_ranges": []
            },
            "pred": {"day": "Tuesday", "start_time": "14:30", "end_time": "16:30"}
        },
        {
            "name": "Disallowed time conflict",
            "constraints": {
                "meeting_duration": 1.0,
                "disallowed_ranges": [{"day": "Tuesday", "start": 14.0, "end": 16.0}]
            },
            "pred": {"day": "Tuesday", "start_time": "14:30", "end_time": "15:30"}
        },
        {
            "name": "Missing fields",
            "constraints": {"meeting_duration": 1.0},
            "pred": {"day": "Tuesday"}
        }
    ]
    
    for test_case in test_cases:
        print(f"\n--- {test_case['name']} ---")
        
        # Plan evaluation
        plan_result, plan_violations = plan_evaluate_calendar(test_case["constraints"], test_case["pred"])
        
        # SMT evaluation
        smt_result, smt_violations = smt_evaluate_calendar(test_case["constraints"], test_case["pred"])
        
        print(f"Plan: {plan_result} - {plan_violations}")
        print(f"SMT:  {smt_result} - {smt_violations}")
        
        if plan_result != smt_result:
            print("❌ INCONSISTENT RESULTS")
        else:
            print("✅ Consistent results")

def compare_meeting_evaluation():
    print("\n=== Meeting Evaluation Comparison ===")
    
    # Test cases for meeting
    test_cases = [
        {
            "name": "Valid meeting with num_people_to_meet",
            "constraints": {
                "num_people_to_meet": 2,
                "people_to_meet": [
                    {"name": "Alice", "location": "A", "time_of_day": {"from": "10:00AM", "to": "12:00PM"}},
                    {"name": "Bob", "location": "B", "time_of_day": {"from": "2:00PM", "to": "4:00PM"}}
                ],
                "start": {"location": "Start", "time_of_day": "9:00AM"},
                "travel_distances": [
                    {"place": {"from": "Start", "to": "A"}, "walking_time": 30},
                    {"place": {"from": "A", "to": "B"}, "walking_time": 60}
                ]
            },
            "pred": {
                "itinerary": [
                    {"person": "Alice", "start_time": "10:30", "end_time": "11:30"},
                    {"person": "Bob", "start_time": "2:30", "end_time": "3:30"}
                ]
            }
        },
        {
            "name": "Insufficient people met",
            "constraints": {
                "num_people_to_meet": 3,
                "people_to_meet": [
                    {"name": "Alice", "location": "A", "time_of_day": {"from": "10:00AM", "to": "12:00PM"}},
                    {"name": "Bob", "location": "B", "time_of_day": {"from": "2:00PM", "to": "4:00PM"}},
                    {"name": "Charlie", "location": "C", "time_of_day": {"from": "4:00PM", "to": "6:00PM"}}
                ],
                "start": {"location": "Start", "time_of_day": "9:00AM"},
                "travel_distances": []
            },
            "pred": {
                "itinerary": [
                    {"person": "Alice", "start_time": "10:30", "end_time": "11:30"},
                    {"person": "Bob", "start_time": "2:30", "end_time": "3:30"}
                ]
            }
        },
        {
            "name": "Invalid time format",
            "constraints": {
                "num_people_to_meet": 1,
                "people_to_meet": [
                    {"name": "Alice", "location": "A", "time_of_day": {"from": "10:00AM", "to": "12:00PM"}}
                ],
                "start": {"location": "Start", "time_of_day": "9:00AM"},
                "travel_distances": []
            },
            "pred": {
                "itinerary": [
                    {"person": "Alice", "start_time": "invalid", "end_time": "11:30"}
                ]
            }
        }
    ]
    
    for test_case in test_cases:
        print(f"\n--- {test_case['name']} ---")
        
        # Plan evaluation
        plan_result, plan_violations = plan_evaluate_meeting(test_case["constraints"], test_case["pred"])
        
        # SMT evaluation
        smt_result, smt_violations = smt_evaluate_meeting(test_case["constraints"], test_case["pred"])
        
        print(f"Plan: {plan_result} - {plan_violations}")
        print(f"SMT:  {smt_result} - {smt_violations}")
        
        if plan_result != smt_result:
            print("❌ INCONSISTENT RESULTS")
        else:
            print("✅ Consistent results")

def compare_trip_evaluation():
    print("\n=== Trip Evaluation Comparison ===")
    
    # Test cases for trip
    test_cases = [
        {
            "name": "Valid trip",
            "constraints": {
                "trip_length": 3,
                "stay_days": {"Paris": 2, "London": 1},
                "direct_flights": [{"from": "Paris", "to": "London"}],
                "city_day_ranges": []
            },
            "pred": {
                "itinerary": [
                    {"day_range": "Day 1-2", "place": "Paris"},
                    {"day_range": "Day 3-3", "place": "London"}
                ]
            }
        },
        {
            "name": "Invalid trip length",
            "constraints": {
                "trip_length": 3,
                "stay_days": {"Paris": 2, "London": 1},
                "direct_flights": [{"from": "Paris", "to": "London"}],
                "city_day_ranges": []
            },
            "pred": {
                "itinerary": [
                    {"day_range": "Day 1-2", "place": "Paris"},
                    {"day_range": "Day 3-4", "place": "London"}
                ]
            }
        },
        {
            "name": "Invalid day range format",
            "constraints": {
                "trip_length": 2,
                "stay_days": {"Paris": 2},
                "direct_flights": [],
                "city_day_ranges": []
            },
            "pred": {
                "itinerary": [
                    {"day_range": "Invalid", "place": "Paris"}
                ]
            }
        }
    ]
    
    for test_case in test_cases:
        print(f"\n--- {test_case['name']} ---")
        
        # Plan evaluation
        plan_result, plan_violations = plan_evaluate_trip(test_case["constraints"], test_case["pred"])
        
        # SMT evaluation
        smt_result, smt_violations = smt_evaluate_trip(test_case["constraints"], test_case["pred"])
        
        print(f"Plan: {plan_result} - {plan_violations}")
        print(f"SMT:  {smt_result} - {smt_violations}")
        
        if plan_result != smt_result:
            print("❌ INCONSISTENT RESULTS")
        else:
            print("✅ Consistent results")

def main():
    print("Comparing constraint evaluation criteria between Plan and SMT refinement programs...")
    
    compare_calendar_evaluation()
    compare_meeting_evaluation()
    compare_trip_evaluation()
    
    print("\n=== Summary ===")
    print("This comparison checks if both programs evaluate the same constraints in the same way.")
    print("Inconsistencies indicate that the programs may have different evaluation criteria.")

if __name__ == "__main__":
    main() 
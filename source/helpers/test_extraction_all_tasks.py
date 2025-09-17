#!/usr/bin/env python3

import sys
import os
import json

sys.path.append('.')
from iterative_plan_refinement_parallel import extract_answer_from_text, evaluate_calendar, evaluate_trip, evaluate_meeting, load_constraints

def test_calendar_extraction():
    """Test calendar extraction"""
    print("=== Testing Calendar Extraction ===")
    
    # Example calendar output
    calendar_output = """SOLUTION:
Based on the constraints, I need to schedule a 0.5-hour meeting on Monday, avoiding the disallowed time ranges.

Looking at the disallowed ranges for Monday:
- 0:00 to 9:00 (9 hours)
- 9:00 to 9:30 (0.5 hours)
- 9:30 to 10:00 (0.5 hours)
- 10:00 to 10:30 (0.5 hours)
- 10:30 to 11:00 (0.5 hours)
- 11:00 to 11:30 (0.5 hours)
- 11:30 to 12:00 (0.5 hours)
- 12:00 to 12:30 (0.5 hours)
- 12:30 to 13:00 (0.5 hours)
- 13:00 to 13:30 (0.5 hours)
- 13:30 to 14:00 (0.5 hours)
- 14:00 to 14:30 (0.5 hours)
- 14:30 to 15:00 (0.5 hours)
- 15:00 to 15:30 (0.5 hours)
- 15:30 to 16:00 (0.5 hours)

The first available slot is 16:00 to 16:30.

{"time_range": "{16:00:16:30}", "day": "Monday"}"""
    
    print("Input text:")
    print(calendar_output)
    print("\n" + "="*50)
    
    # Test extraction
    extracted = extract_answer_from_text(calendar_output, "calendar")
    print(f"Extracted result: {extracted}")
    
    if extracted:
        print("✓ Calendar extraction successful!")
        
        # Test evaluation with constraints
        constraints = load_constraints("calendar")
        example_id = "calendar_scheduling_example_1"
        if example_id in constraints:
            example_constraints = constraints[example_id]
            result, violations = evaluate_calendar(example_constraints, extracted)
            print(f"Evaluation result: {result}")
            print(f"Violations: {violations}")
            
            if result:
                print("✓ Calendar evaluation passed!")
            else:
                print("✗ Calendar evaluation failed!")
        else:
            print(f"✗ Example {example_id} not found in constraints")
    else:
        print("✗ Calendar extraction failed!")

def test_trip_extraction():
    """Test trip extraction"""
    print("\n=== Testing Trip Extraction ===")
    
    # Example trip output
    trip_output = """SOLUTION:
Based on the constraints, I need to plan a 7-day trip visiting Madrid, Dublin, and Tallinn.

The trip should be:
- Madrid: 4 days (Day 1-4)
- Dublin: 2 days (Day 4-6) 
- Tallinn: 1 day (Day 6-7)

This satisfies all constraints:
- Total trip length: 7 days ✓
- Madrid: 4 days ✓
- Dublin: 2 days ✓
- Tallinn: 1 day ✓
- Direct flights available between all cities ✓

{"itinerary": [{"day_range": "Day 1-4", "place": "Madrid"}, {"day_range": "Day 4-6", "place": "Dublin"}, {"day_range": "Day 6-7", "place": "Tallinn"}]}"""
    
    print("Input text:")
    print(trip_output)
    print("\n" + "="*50)
    
    # Test extraction
    extracted = extract_answer_from_text(trip_output, "trip")
    print(f"Extracted result: {extracted}")
    
    if extracted:
        print("✓ Trip extraction successful!")
        
        # Test evaluation with constraints
        constraints = load_constraints("trip")
        example_id = "trip_planning_example_142"
        if example_id in constraints:
            example_constraints = constraints[example_id]
            result, violations = evaluate_trip(example_constraints, extracted)
            print(f"Evaluation result: {result}")
            print(f"Violations: {violations}")
            
            if result:
                print("✓ Trip evaluation passed!")
            else:
                print("✗ Trip evaluation failed!")
        else:
            print(f"✗ Example {example_id} not found in constraints")
    else:
        print("✗ Trip extraction failed!")

def test_meeting_extraction():
    """Test meeting extraction"""
    print("\n=== Testing Meeting Extraction ===")
    
    # Example meeting output
    meeting_output = """SOLUTION:
Based on the constraints, I need to meet Kenneth for at least 90 minutes during his availability window (2:15 PM to 7:45 PM).

The optimal schedule is:
- Meet Kenneth from 2:15 PM to 3:45 PM (90 minutes)

This satisfies all constraints:
- Kenneth is available during this time ✓
- Meeting duration is 90 minutes ✓
- Travel time is accounted for ✓

{"itinerary": [{"action": "meet", "person": "Kenneth", "start_time": "14:15", "end_time": "15:45"}]}"""
    
    print("Input text:")
    print(meeting_output)
    print("\n" + "="*50)
    
    # Test extraction
    extracted = extract_answer_from_text(meeting_output, "meeting")
    print(f"Extracted result: {extracted}")
    
    if extracted:
        print("✓ Meeting extraction successful!")
        
        # Test evaluation with constraints
        constraints = load_constraints("meeting")
        example_id = "meeting_planning_example_6"
        if example_id in constraints:
            example_constraints = constraints[example_id]
            result, violations = evaluate_meeting(example_constraints, extracted)
            print(f"Evaluation result: {result}")
            print(f"Violations: {violations}")
            
            if result:
                print("✓ Meeting evaluation passed!")
            else:
                print("✗ Meeting evaluation failed!")
        else:
            print(f"✗ Example {example_id} not found in constraints")
    else:
        print("✗ Meeting extraction failed!")

def main():
    """Test all task types"""
    print("Testing LLM-based Answer Extraction for All Tasks")
    print("=" * 60)
    
    test_calendar_extraction()
    test_trip_extraction()
    test_meeting_extraction()
    
    print("\n" + "=" * 60)
    print("All tests completed!")

if __name__ == "__main__":
    main() 
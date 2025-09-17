#!/usr/bin/env python3

import sys
import os
import json

sys.path.append('.')
from iterative_plan_refinement_parallel import extract_answer_from_text, evaluate_meeting, load_constraints

def test_meeting_extraction():
    """Test the meeting extraction with the correct format"""
    
    # Example 6 output with correct format (itinerary format)
    example_output = """SOLUTION:
The goal is to meet as many friends as possible, but the only friend specified with availability and location is Kenneth at Nob Hill. Since no other friends or their availabilities are provided, the schedule focuses solely on meeting Kenneth for the required minimum of 90 minutes within his availability window (2:15 PM to 7:45 PM). 

To optimize the schedule:
- Start the meeting as early as possible (2:15 PM) to free up the rest of the day for potential meetings with other friends at Fisherman's Wharf, though none are specified.
- Travel time from Fisherman's Wharf to Nob Hill is 11 minutes, so depart Fisherman's Wharf at 2:04 PM to arrive at Nob Hill by 2:15 PM.
- The meeting lasts 90 minutes, ending at 3:45 PM.
- After the meeting, depart Nob Hill at 3:45 PM and arrive back at Fisherman's Wharf at 3:56 PM, allowing time to meet friends there for the remainder of the day.

This schedule ensures the meeting with Kenneth is satisfied and maximizes potential time at Fisherman's Wharf for other activities or meetings, given the constraints.

{"itinerary": [{"action": "meet", "person": "Kenneth", "start_time": "14:15", "end_time": "15:45"}]}"""

    print("=== Testing Meeting Extraction (Correct Format) ===")
    print("Input text:")
    print(example_output)
    print("\n" + "="*50)
    
    # Test extraction
    extracted = extract_answer_from_text(example_output, "meeting")
    print(f"Extracted result: {extracted}")
    
    if extracted:
        print("✓ Extraction successful!")
        
        # Test evaluation with constraints
        constraints = load_constraints("meeting")
        example_id = "meeting_planning_example_6"
        if example_id in constraints:
            example_constraints = constraints[example_id]
            print(f"\nConstraints for {example_id}:")
            print(f"People to meet: {example_constraints.get('people_to_meet', [])}")
            
            result, violations = evaluate_meeting(example_constraints, extracted)
            print(f"\nEvaluation result: {result}")
            print(f"Violations: {violations}")
            
            if result:
                print("✓ Evaluation passed!")
            else:
                print("✗ Evaluation failed!")
        else:
            print(f"✗ Example {example_id} not found in constraints")
    else:
        print("✗ Extraction failed!")

def test_meeting_extraction_old_format():
    """Test the meeting extraction with the old format (meetings key)"""
    
    # Example 6 output with old format (meetings key)
    example_output_old = """SOLUTION:
The goal is to meet as many friends as possible, but the only friend specified with availability and location is Kenneth at Nob Hill. Since no other friends or their availabilities are provided, the schedule focuses solely on meeting Kenneth for the required minimum of 90 minutes within his availability window (2:15 PM to 7:45 PM). 

To optimize the schedule:
- Start the meeting as early as possible (2:15 PM) to free up the rest of the day for potential meetings with other friends at Fisherman's Wharf, though none are specified.
- Travel time from Fisherman's Wharf to Nob Hill is 11 minutes, so depart Fisherman's Wharf at 2:04 PM to arrive at Nob Hill by 2:15 PM.
- The meeting lasts 90 minutes, ending at 3:45 PM.
- After the meeting, depart Nob Hill at 3:45 PM and arrive back at Fisherman's Wharf at 3:56 PM, allowing time to meet friends there for the remainder of the day.

This schedule ensures the meeting with Kenneth is satisfied and maximizes potential time at Fisherman's Wharf for other activities or meetings, given the constraints.

{"meetings": [{"person": "Kenneth", "start_time": "2:15PM", "end_time": "3:45PM"}]}"""

    print("\n=== Testing Meeting Extraction (Old Format) ===")
    print("Input text (old format with meetings key):")
    print(example_output_old)
    print("\n" + "="*50)
    
    # Test extraction
    extracted = extract_answer_from_text(example_output_old, "meeting")
    print(f"Extracted result: {extracted}")
    
    if extracted:
        print("✓ Extraction successful!")
        
        # Test evaluation with constraints
        constraints = load_constraints("meeting")
        example_id = "meeting_planning_example_6"
        if example_id in constraints:
            example_constraints = constraints[example_id]
            result, violations = evaluate_meeting(example_constraints, extracted)
            print(f"\nEvaluation result: {result}")
            print(f"Violations: {violations}")
            
            if result:
                print("✓ Evaluation passed!")
            else:
                print("✗ Evaluation failed!")
        else:
            print(f"✗ Example {example_id} not found in constraints")
    else:
        print("✗ Extraction failed!")

def test_gold_extraction():
    """Test gold answer extraction"""
    print("\n=== Testing Gold Answer Extraction ===")
    
    # Load an example
    with open("../data/meeting_planning_100.json", 'r') as f:
        examples = json.load(f)
    
    example_id = "meeting_planning_example_6"
    if example_id in examples:
        example = examples[example_id]
        print(f"Gold plan for {example_id}:")
        print(example.get("golden_plan", "No golden plan"))
        
        from iterative_plan_refinement_parallel import extract_gold_answer
        gold_extracted = extract_gold_answer(example, "meeting")
        print(f"\nExtracted gold: {gold_extracted}")
    else:
        print(f"Example {example_id} not found")

if __name__ == "__main__":
    test_meeting_extraction()
    test_meeting_extraction_old_format()
    test_gold_extraction() 
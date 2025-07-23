#!/usr/bin/env python3

import json
import sys
import os
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

from iterative_smt_refinement_enhanced import evaluate_meeting

def test_meeting_constraint_evaluation():
    """Test the meeting constraint evaluation for the problematic example"""
    
    # Load the constraints for meeting_planning_example_911
    with open("../data/meeting_planning_100_constraints.json", "r") as f:
        constraints_data = json.load(f)
    
    example_id = "meeting_planning_example_911"
    constraints = constraints_data[example_id]["constraints"]
    
    print(f"Testing constraints for {example_id}")
    print(f"Constraints: {json.dumps(constraints, indent=2)}")
    
    # The predicted plan from the evaluation.json
    pred_dict = {
        "itinerary": [
            {
                "action": "meet",
                "person": "Nancy",
                "start_time": "08:15",
                "end_time": "09:45"
            },
            {
                "action": "meet",
                "person": "Stephanie",
                "start_time": "10:15",
                "end_time": "11:30"
            },
            {
                "action": "meet",
                "person": "David",
                "start_time": "11:15",
                "end_time": "13:15"
            },
            {
                "action": "meet",
                "person": "Elizabeth",
                "start_time": "11:30",
                "end_time": "12:30"
            },
            {
                "action": "meet",
                "person": "Robert",
                "start_time": "13:15",
                "end_time": "14:00"
            },
            {
                "action": "meet",
                "person": "Melissa",
                "start_time": "14:00",
                "end_time": "14:30"
            },
            {
                "action": "meet",
                "person": "Brian",
                "start_time": "14:15",
                "end_time": "16:00"
            },
            {
                "action": "meet",
                "person": "James",
                "start_time": "15:00",
                "end_time": "17:00"
            },
            {
                "action": "meet",
                "person": "Sarah",
                "start_time": "17:00",
                "end_time": "18:15"
            },
            {
                "action": "meet",
                "person": "Steven",
                "start_time": "17:30",
                "end_time": "17:45"
            }
        ]
    }
    
    print(f"\nPredicted plan: {json.dumps(pred_dict, indent=2)}")
    
    # Test the constraint evaluation
    try:
        constraints_satisfied, violated_constraints = evaluate_meeting(constraints, pred_dict)
        print(f"\nResult:")
        print(f"  constraints_satisfied: {constraints_satisfied}")
        print(f"  violated_constraints: {json.dumps(violated_constraints, indent=2)}")
        
        if not constraints_satisfied and not violated_constraints:
            print("\n*** BUG FOUND: constraints_satisfied=False but violated_constraints is empty! ***")
            
    except Exception as e:
        print(f"Exception during evaluation: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    test_meeting_constraint_evaluation() 
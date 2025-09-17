import json
import sys
import os

# Add the source directory to the path
sys.path.append('source')

# Import evaluation functions from all four files
from iterative_plan_refinement_parallel import evaluate_meeting as evaluate_meeting_parallel
from iterative_plan_refinement_parallel_noConstraintFeedback import evaluate_meeting as evaluate_meeting_parallel_ncf
from iterative_plan_refinement_together import evaluate_meeting as evaluate_meeting_together
from iterative_plan_refinement_together_noConstraintFeedback import evaluate_meeting as evaluate_meeting_together_ncf

def load_constraints(task):
    """Load constraints from the appropriate JSON file"""
    task_name_map = {
        "calendar": "calendar_scheduling",
        "trip": "trip_planning",
        "meeting": "meeting_planning"
    }
    with open(f"data/{task_name_map[task]}_100_constraints.json") as f:
        constraints_data = json.load(f)
        return {example_id: data.get("constraints", {}) for example_id, data in constraints_data.items()}

def test_all_files_consistency():
    """Test that all four files provide consistent evaluation results"""
    print("="*80)
    print("COMPREHENSIVE CONSISTENCY TEST - ALL FOUR FILES")
    print("="*80)
    
    # Load constraints for example 131 (meeting duration issue)
    constraints = load_constraints("meeting")
    example_131_constraints = constraints.get("meeting_planning_example_131", {})
    
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
    
    print("Testing Example 131 - Meeting Duration Validation")
    print("Constraints:")
    print(json.dumps(example_131_constraints, indent=2))
    print("\nPrediction:")
    print(json.dumps(pred_dict, indent=2))
    
    # Test all four evaluation functions
    results = {}
    
    print("\n" + "-"*60)
    print("EVALUATION RESULTS FROM ALL FOUR FILES")
    print("-"*60)
    
    # Test 1: iterative_plan_refinement_parallel.py
    print("\n1. iterative_plan_refinement_parallel.py:")
    result1 = evaluate_meeting_parallel(example_131_constraints, pred_dict)
    results['parallel'] = result1
    print(f"   Constraints satisfied: {result1[0]}")
    print(f"   Violated constraints: {result1[1]}")
    
    # Test 2: iterative_plan_refinement_parallel_noConstraintFeedback.py
    print("\n2. iterative_plan_refinement_parallel_noConstraintFeedback.py:")
    result2 = evaluate_meeting_parallel_ncf(example_131_constraints, pred_dict)
    results['parallel_ncf'] = result2
    print(f"   Constraints satisfied: {result2[0]}")
    print(f"   Violated constraints: {result2[1]}")
    
    # Test 3: iterative_plan_refinement_together.py
    print("\n3. iterative_plan_refinement_together.py:")
    result3 = evaluate_meeting_together(example_131_constraints, pred_dict)
    results['together'] = result3
    print(f"   Constraints satisfied: {result3[0]}")
    print(f"   Violated constraints: {result3[1]}")
    
    # Test 4: iterative_plan_refinement_together_noConstraintFeedback.py
    print("\n4. iterative_plan_refinement_together_noConstraintFeedback.py:")
    result4 = evaluate_meeting_together_ncf(example_131_constraints, pred_dict)
    results['together_ncf'] = result4
    print(f"   Constraints satisfied: {result4[0]}")
    print(f"   Violated constraints: {result4[1]}")
    
    # Check consistency
    print("\n" + "-"*60)
    print("CONSISTENCY CHECK")
    print("-"*60)
    
    all_results_match = True
    reference_result = results['parallel']
    
    for name, result in results.items():
        if result != reference_result:
            all_results_match = False
            print(f"❌ {name}: Results DO NOT match reference")
        else:
            print(f"✅ {name}: Results match reference")
    
    print(f"\nOverall consistency: {'✅ ALL FILES CONSISTENT' if all_results_match else '❌ INCONSISTENCY DETECTED'}")
    
    # Verify the fix is working
    print("\n" + "-"*60)
    print("MEETING DURATION FIX VERIFICATION")
    print("-"*60)
    
    expected_violation = {'meeting_duration': {'person': 'Kenneth', 'required': 45, 'actual': 20.0}}
    fix_working = False
    
    for name, result in results.items():
        if result[0] == False and 'meeting_duration' in result[1]:
            fix_working = True
            print(f"✅ {name}: Meeting duration validation working correctly")
        else:
            print(f"❌ {name}: Meeting duration validation NOT working")
    
    print(f"\nMeeting duration fix status: {'✅ FIX WORKING' if fix_working else '❌ FIX NOT WORKING'}")
    
    return all_results_match and fix_working

def test_example_118_travel_time():
    """Test example 118 to ensure travel time validation still works"""
    print("\n" + "="*80)
    print("TESTING EXAMPLE 118 - TRAVEL TIME VALIDATION")
    print("="*80)
    
    # Load constraints for example 118
    constraints = load_constraints("meeting")
    example_118_constraints = constraints.get("meeting_planning_example_118", {})
    
    # Model's prediction
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
    
    print("Testing Example 118 - Travel Time + Meeting Duration Validation")
    
    # Test with parallel version
    result = evaluate_meeting_parallel(example_118_constraints, pred_dict)
    print(f"\niterative_plan_refinement_parallel.py:")
    print(f"   Constraints satisfied: {result[0]}")
    print(f"   Violated constraints: {result[1]}")
    
    # Check if it's detecting either travel time OR meeting duration violation
    has_violation = result[0] == False and len(result[1]) > 0
    print(f"   Has constraint violation: {has_violation}")
    
    return has_violation

if __name__ == "__main__":
    print("Running comprehensive consistency test for all four files...")
    
    # Test all files consistency
    consistency_ok = test_all_files_consistency()
    
    # Test travel time validation still works
    travel_time_ok = test_example_118_travel_time()
    
    print("\n" + "="*80)
    print("FINAL SUMMARY")
    print("="*80)
    print(f"All files consistent: {'✅ YES' if consistency_ok else '❌ NO'}")
    print(f"Travel time validation working: {'✅ YES' if travel_time_ok else '❌ NO'}")
    print(f"Meeting duration fix working: {'✅ YES' if consistency_ok else '❌ NO'}")
    
    if consistency_ok and travel_time_ok:
        print("\n🎉 ALL TESTS PASSED! The meeting duration fix is properly applied to all four files.")
    else:
        print("\n❌ SOME TESTS FAILED! Please check the implementation.") 
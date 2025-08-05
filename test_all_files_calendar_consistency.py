import json
import sys
import os

# Add the source directory to the path
sys.path.append('source')

# Import evaluation functions from all four files
from iterative_plan_refinement_parallel import evaluate_calendar as evaluate_calendar_parallel
from iterative_plan_refinement_parallel_noConstraintFeedback import evaluate_calendar as evaluate_calendar_parallel_ncf
from iterative_plan_refinement_together import evaluate_calendar as evaluate_calendar_together
from iterative_plan_refinement_together_noConstraintFeedback import evaluate_calendar as evaluate_calendar_together_ncf

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

def test_all_files_calendar_consistency():
    """Test that all four files provide consistent calendar evaluation results"""
    print("="*80)
    print("COMPREHENSIVE CALENDAR CONSISTENCY TEST - ALL FOUR FILES")
    print("="*80)
    
    # Load constraints for example 398
    constraints = load_constraints("calendar")
    example_398_constraints = constraints.get("calendar_scheduling_example_398", {})
    
    # Test case: time_range format (the problematic case from the user)
    pred_dict = {
        "time_range": "13:00:13:30",
        "day": "Monday"
    }
    
    print("Testing Example 398 - Calendar Time Range Format")
    print("Constraints:")
    print(json.dumps(example_398_constraints, indent=2))
    print("\nPrediction:")
    print(json.dumps(pred_dict, indent=2))
    
    # Test all four evaluation functions
    results = {}
    
    print("\n" + "-"*60)
    print("EVALUATION RESULTS FROM ALL FOUR FILES")
    print("-"*60)
    
    # Test 1: iterative_plan_refinement_parallel.py
    print("\n1. iterative_plan_refinement_parallel.py:")
    result1 = evaluate_calendar_parallel(example_398_constraints, pred_dict)
    results['parallel'] = result1
    print(f"   Constraints satisfied: {result1[0]}")
    print(f"   Violated constraints: {result1[1]}")
    
    # Test 2: iterative_plan_refinement_parallel_noConstraintFeedback.py
    print("\n2. iterative_plan_refinement_parallel_noConstraintFeedback.py:")
    result2 = evaluate_calendar_parallel_ncf(example_398_constraints, pred_dict)
    results['parallel_ncf'] = result2
    print(f"   Constraints satisfied: {result2[0]}")
    print(f"   Violated constraints: {result2[1]}")
    
    # Test 3: iterative_plan_refinement_together.py
    print("\n3. iterative_plan_refinement_together.py:")
    result3 = evaluate_calendar_together(example_398_constraints, pred_dict)
    results['together'] = result3
    print(f"   Constraints satisfied: {result3[0]}")
    print(f"   Violated constraints: {result3[1]}")
    
    # Test 4: iterative_plan_refinement_together_noConstraintFeedback.py
    print("\n4. iterative_plan_refinement_together_noConstraintFeedback.py:")
    result4 = evaluate_calendar_together_ncf(example_398_constraints, pred_dict)
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
    print("CALENDAR FORMAT FIX VERIFICATION")
    print("-"*60)
    
    expected_result = (True, {})  # Should be satisfied for this valid time slot
    fix_working = False
    
    for name, result in results.items():
        if result == expected_result:
            fix_working = True
            print(f"✅ {name}: Calendar format fix working correctly")
        else:
            print(f"❌ {name}: Calendar format fix NOT working")
    
    print(f"\nCalendar format fix status: {'✅ FIX WORKING' if fix_working else '❌ FIX NOT WORKING'}")
    
    return all_results_match and fix_working

def test_example_398_original_issue():
    """Test the exact case from the user's evaluation.json file"""
    print("\n" + "="*80)
    print("TESTING EXAMPLE 398 - ORIGINAL ISSUE")
    print("="*80)
    
    # Load constraints for example 398
    constraints = load_constraints("calendar")
    example_398_constraints = constraints.get("calendar_scheduling_example_398", {})
    
    # The exact prediction from the user's evaluation.json file
    pred_dict = {
        "time_range": "13:00:13:30",
        "day": "Monday"
    }
    
    print("Original Issue - Example 398:")
    print("Prediction from evaluation.json:")
    print(json.dumps(pred_dict, indent=2))
    
    # Test with parallel version
    result = evaluate_calendar_parallel(example_398_constraints, pred_dict)
    print(f"\niterative_plan_refinement_parallel.py:")
    print(f"   Constraints satisfied: {result[0]}")
    print(f"   Violated constraints: {result[1]}")
    
    # Check if the issue is resolved
    issue_resolved = result[0] == True and result[1] == {}
    print(f"   Original issue resolved: {issue_resolved}")
    
    if issue_resolved:
        print("   ✅ The 'missing_fields' error should no longer occur!")
    else:
        print("   ❌ The issue is still present")
    
    return issue_resolved

if __name__ == "__main__":
    print("Running comprehensive calendar consistency test for all four files...")
    
    # Test all files consistency
    consistency_ok = test_all_files_calendar_consistency()
    
    # Test the original issue
    original_issue_resolved = test_example_398_original_issue()
    
    print("\n" + "="*80)
    print("FINAL SUMMARY")
    print("="*80)
    print(f"All files consistent: {'✅ YES' if consistency_ok else '❌ NO'}")
    print(f"Original issue resolved: {'✅ YES' if original_issue_resolved else '❌ NO'}")
    print(f"Calendar format fix working: {'✅ YES' if consistency_ok else '❌ NO'}")
    
    if consistency_ok and original_issue_resolved:
        print("\n🎉 ALL TESTS PASSED! The calendar evaluation format fix is properly applied to all four files.")
        print("The 'missing_fields' error for time_range format should no longer occur.")
    else:
        print("\n❌ SOME TESTS FAILED! Please check the implementation.") 
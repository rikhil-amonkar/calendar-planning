import json
import sys
import os

# Add the source directory to the path
sys.path.append('source')

from iterative_plan_refinement_parallel import evaluate_calendar as evaluate_calendar_parallel
from iterative_plan_refinement_parallel_noConstraintFeedback import evaluate_calendar as evaluate_calendar_parallel_ncf

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

def test_calendar_evaluation_fix():
    """Test that calendar evaluation handles both time_range and start_time/end_time formats"""
    print("="*80)
    print("CALENDAR EVALUATION FORMAT FIX TEST")
    print("="*80)
    
    # Load constraints for example 398
    constraints = load_constraints("calendar")
    example_398_constraints = constraints.get("calendar_scheduling_example_398", {})
    
    print("Constraints for example 398:")
    print(json.dumps(example_398_constraints, indent=2))
    
    # Test 1: time_range format (the problematic case)
    pred_dict_time_range = {
        "time_range": "13:00:13:30",
        "day": "Monday"
    }
    
    print("\n" + "-"*60)
    print("TEST 1: time_range format")
    print("-"*60)
    print("Prediction (time_range format):")
    print(json.dumps(pred_dict_time_range, indent=2))
    
    # Test with both parallel versions
    print("\n=== Testing iterative_plan_refinement_parallel.py ===")
    result1 = evaluate_calendar_parallel(example_398_constraints, pred_dict_time_range)
    print(f"Constraints satisfied: {result1[0]}")
    print(f"Violated constraints: {result1[1]}")
    
    print("\n=== Testing iterative_plan_refinement_parallel_noConstraintFeedback.py ===")
    result2 = evaluate_calendar_parallel_ncf(example_398_constraints, pred_dict_time_range)
    print(f"Constraints satisfied: {result2[0]}")
    print(f"Violated constraints: {result2[1]}")
    
    # Test 2: time_range format with curly braces
    pred_dict_time_range_braces = {
        "time_range": "{13:00:13:30}",
        "day": "Monday"
    }
    
    print("\n" + "-"*60)
    print("TEST 2: time_range format with curly braces")
    print("-"*60)
    print("Prediction (time_range format with braces):")
    print(json.dumps(pred_dict_time_range_braces, indent=2))
    
    print("\n=== Testing iterative_plan_refinement_parallel.py ===")
    result3 = evaluate_calendar_parallel(example_398_constraints, pred_dict_time_range_braces)
    print(f"Constraints satisfied: {result3[0]}")
    print(f"Violated constraints: {result3[1]}")
    
    print("\n=== Testing iterative_plan_refinement_parallel_noConstraintFeedback.py ===")
    result4 = evaluate_calendar_parallel_ncf(example_398_constraints, pred_dict_time_range_braces)
    print(f"Constraints satisfied: {result4[0]}")
    print(f"Violated constraints: {result4[1]}")
    
    # Test 3: start_time/end_time format (original format)
    pred_dict_start_end = {
        "start_time": "13:00",
        "end_time": "13:30",
        "day": "Monday"
    }
    
    print("\n" + "-"*60)
    print("TEST 3: start_time/end_time format")
    print("-"*60)
    print("Prediction (start_time/end_time format):")
    print(json.dumps(pred_dict_start_end, indent=2))
    
    print("\n=== Testing iterative_plan_refinement_parallel.py ===")
    result5 = evaluate_calendar_parallel(example_398_constraints, pred_dict_start_end)
    print(f"Constraints satisfied: {result5[0]}")
    print(f"Violated constraints: {result5[1]}")
    
    print("\n=== Testing iterative_plan_refinement_parallel_noConstraintFeedback.py ===")
    result6 = evaluate_calendar_parallel_ncf(example_398_constraints, pred_dict_start_end)
    print(f"Constraints satisfied: {result6[0]}")
    print(f"Violated constraints: {result6[1]}")
    
    # Test 4: Invalid format
    pred_dict_invalid = {
        "time_range": "invalid_format",
        "day": "Monday"
    }
    
    print("\n" + "-"*60)
    print("TEST 4: Invalid time_range format")
    print("-"*60)
    print("Prediction (invalid format):")
    print(json.dumps(pred_dict_invalid, indent=2))
    
    print("\n=== Testing iterative_plan_refinement_parallel.py ===")
    result7 = evaluate_calendar_parallel(example_398_constraints, pred_dict_invalid)
    print(f"Constraints satisfied: {result7[0]}")
    print(f"Violated constraints: {result7[1]}")
    
    print("\n=== Testing iterative_plan_refinement_parallel_noConstraintFeedback.py ===")
    result8 = evaluate_calendar_parallel_ncf(example_398_constraints, pred_dict_invalid)
    print(f"Constraints satisfied: {result8[0]}")
    print(f"Violated constraints: {result8[1]}")
    
    # Summary
    print("\n" + "="*80)
    print("SUMMARY")
    print("="*80)
    
    # Check if the fix is working
    time_range_working = result1[0] == True and result2[0] == True
    time_range_braces_working = result3[0] == True and result4[0] == True
    start_end_working = result5[0] == True and result6[0] == True
    invalid_handled = result7[0] == False and result8[0] == False
    
    print(f"✅ time_range format working: {time_range_working}")
    print(f"✅ time_range with braces working: {time_range_braces_working}")
    print(f"✅ start_time/end_time format working: {start_end_working}")
    print(f"✅ invalid format handled correctly: {invalid_handled}")
    
    all_working = time_range_working and time_range_braces_working and start_end_working and invalid_handled
    
    if all_working:
        print("\n🎉 ALL TESTS PASSED! Calendar evaluation format fix is working correctly.")
    else:
        print("\n❌ SOME TESTS FAILED! Please check the implementation.")
    
    return all_working

if __name__ == "__main__":
    test_calendar_evaluation_fix() 
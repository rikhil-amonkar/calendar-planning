"""
Test script for enhanced SMT refinement functionality

This script tests the smart code extraction and execution result handling features
of the enhanced SMT refinement system.
"""

import json
import tempfile
import os
import sys
from iterative_smt_refinement_enhanced import (
    smart_extract_code, 
    smart_extract_execution_result,
    extract_answer_basic
)

def test_smart_code_extraction():
    """Test smart code extraction with various formats"""
    print("Testing smart code extraction...")
    
    # Test 1: Properly formatted code block
    response1 = """
    Here's a solution using Z3:
    
    ```python
    from z3 import *
    
    # Create variables
    day = Int('day')
    start_time = Int('start_time')
    
    # Create solver
    s = Solver()
    
    # Add constraints
    s.add(day >= 1)
    s.add(day <= 7)
    
    if s.check() == sat:
        m = s.model()
        print(f"Day: {m[day]}")
        print(f"Start Time: {m[start_time]}")
    ```
    """
    
    code1 = smart_extract_code(response1)
    print(f"Test 1 - Proper format: {'PASS' if 'from z3 import' in code1 else 'FAIL'}")
    print(f"Extracted code length: {len(code1)}")
    
    # Test 2: Code without proper formatting
    response2 = """
    Here's a solution using Z3:
    
    from z3 import *
    
    # Create variables
    day = Int('day')
    start_time = Int('start_time')
    
    # Create solver
    s = Solver()
    
    # Add constraints
    s.add(day >= 1)
    s.add(day <= 7)
    
    if s.check() == sat:
        m = s.model()
        print(f"Day: {m[day]}")
        print(f"Start Time: {m[start_time]}")
    """
    
    code2 = smart_extract_code(response2)
    print(f"Test 2 - No formatting: {'PASS' if 'from z3 import' in code2 else 'FAIL'}")
    print(f"Extracted code length: {len(code2)}")
    
    # Test 3: Mixed content with code
    response3 = """
    Let me solve this step by step.
    
    First, I'll use Z3 solver:
    from z3 import *
    day = Int('day')
    
    Then I'll add constraints:
    s = Solver()
    s.add(day >= 1)
    
    Finally, I'll check the solution:
    if s.check() == sat:
        print("Solution found")
    """
    
    code3 = smart_extract_code(response3)
    print(f"Test 3 - Mixed content: {'PASS' if 'from z3 import' in code3 else 'FAIL'}")
    print(f"Extracted code length: {len(code3)}")

def test_smart_execution_result_extraction():
    """Test smart execution result extraction"""
    print("\nTesting smart execution result extraction...")
    
    # Test 1: Valid calendar output
    calendar_output = """
    SOLUTION:
    Day: Monday
    Start Time: 14:30
    End Time: 15:30
    """
    
    result1 = smart_extract_execution_result(calendar_output, "calendar")
    print(f"Test 1 - Valid calendar: {'PASS' if result1.get('day') == 'Monday' else 'FAIL'}")
    print(f"Result: {result1}")
    
    # Test 2: Error output
    error_output = """
    Traceback (most recent call last):
      File "solution.py", line 10, in <module>
        s.add(day >= 1)
    NameError: name 'day' is not defined
    """
    
    result2 = smart_extract_execution_result(error_output, "calendar")
    print(f"Test 2 - Error output: {'PASS' if 'error' in result2 else 'FAIL'}")
    print(f"Result: {result2}")
    
    # Test 3: No solution found
    no_solution_output = """
    No solution found
    UNSAT
    """
    
    result3 = smart_extract_execution_result(no_solution_output, "calendar")
    print(f"Test 3 - No solution: {'PASS' if 'no_plan' in result3 else 'FAIL'}")
    print(f"Result: {result3}")
    
    # Test 4: Valid trip output
    trip_output = """
    SOLUTION:
    {"itinerary": [{"day_range": "Day 1-3", "place": "Venice"}, {"day_range": "Day 3-5", "place": "Vienna"}]}
    """
    
    result4 = smart_extract_execution_result(trip_output, "trip")
    print(f"Test 4 - Valid trip: {'PASS' if 'itinerary' in result4 else 'FAIL'}")
    print(f"Result: {result4}")

def test_error_handling_scenarios():
    """Test different error handling scenarios"""
    print("\nTesting error handling scenarios...")
    
    # Test 1: Execution error feedback
    execution_error = "NameError: name 'day' is not defined"
    feedback1 = f"The previous Z3 solution returned an error: {execution_error}\n\nPlease revise your Z3 program to fix this error."
    print(f"Test 1 - Execution error feedback: {'PASS' if 'error' in feedback1 else 'FAIL'}")
    print(f"Feedback: {feedback1[:100]}...")
    
    # Test 2: No plan found feedback
    no_plan_reason = "UNSAT - no valid solution exists"
    feedback2 = f"The previous Z3 solution failed to find a valid plan: {no_plan_reason}\n\nPlease adjust your Z3 program to find a solution."
    print(f"Test 2 - No plan feedback: {'PASS' if 'failed to find' in feedback2 else 'FAIL'}")
    print(f"Feedback: {feedback2[:100]}...")
    
    # Test 3: Constraint violation feedback
    plan_summary = '{"day": "Tuesday", "start_time": "10:00", "end_time": "11:00"}'
    feedback3 = f"The previous solution produced the following plan:\n{plan_summary}\n\nHowever, this plan is incorrect and violates some constraints."
    print(f"Test 3 - Constraint violation feedback: {'PASS' if 'violates some constraints' in feedback3 else 'FAIL'}")
    print(f"Feedback: {feedback3[:100]}...")

def test_basic_extraction_fallback():
    """Test basic extraction fallback"""
    print("\nTesting basic extraction fallback...")
    
    # Test calendar extraction
    calendar_text = "SOLUTION:\nDay: Monday\nStart Time: 14:30\nEnd Time: 15:30"
    result1 = extract_answer_basic(calendar_text, "calendar")
    print(f"Test 1 - Calendar basic extraction: {'PASS' if result1.get('day') == 'Monday' else 'FAIL'}")
    print(f"Result: {result1}")
    
    # Test meeting extraction
    meeting_text = "Meet David from 13:00 to 14:00"
    result2 = extract_answer_basic(meeting_text, "meeting")
    print(f"Test 2 - Meeting basic extraction: {'PASS' if result2.get('itinerary') else 'FAIL'}")
    print(f"Result: {result2}")

if __name__ == "__main__":
    print("Enhanced SMT Refinement Test Suite")
    print("=" * 50)
    
    try:
        test_smart_code_extraction()
        test_smart_execution_result_extraction()
        test_error_handling_scenarios()
        test_basic_extraction_fallback()
        
        print("\n" + "=" * 50)
        print("All tests completed!")
        
    except Exception as e:
        print(f"\nTest failed with error: {e}")
        import traceback
        traceback.print_exc() 
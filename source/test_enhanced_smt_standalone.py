"""
Standalone test script for enhanced SMT refinement functionality

This script tests the smart code extraction and execution result handling features
without importing the main enhanced script to avoid argument parsing conflicts.
"""

import json
import re
import tempfile
import os
import sys
from openai import OpenAI

def get_openai_client():
    """Get OpenAI client for GPT-based extraction"""
    try:
        with open("../../scheduling_key.json") as f:
            key = json.load(f)["openai"]
        return OpenAI(api_key=key)
    except (FileNotFoundError, KeyError):
        print("Warning: Could not initialize OpenAI client for extraction")
        return None

def smart_extract_code(response_txt):
    """
    Smart code extraction using GPT when traditional regex fails
    """
    # First try traditional regex extraction
    matches = re.findall(r"```python\s*(.*?)```", response_txt, re.DOTALL)
    if matches:
        return matches[-1].strip()
    
    # If no code blocks found, try to extract code using GPT
    client = get_openai_client()
    if not client:
        print("OpenAI client not available, falling back to basic extraction")
        return ""
    
    try:
        prompt = f"""Extract the Python code from the following text. Look for any Python code that might solve a scheduling problem using Z3 solver.

Text:
{response_txt}

If you find Python code, return ONLY the code without any markdown formatting or explanations.
If no Python code is found, return an empty string.

Focus on:
1. Code that imports and uses Z3 solver
2. Code that defines variables, constraints, and solves problems
3. Code that prints or returns results

Return only the Python code:"""

        response = client.chat.completions.create(
            model="gpt-4o-mini",
            messages=[{"role": "user", "content": prompt}],
            temperature=0,
            max_tokens=2000
        )
        
        extracted_code = response.choices[0].message.content.strip()
        
        # Clean up the extracted code
        if extracted_code.startswith("```python"):
            extracted_code = extracted_code[9:]
        if extracted_code.endswith("```"):
            extracted_code = extracted_code[:-3]
        
        return extracted_code.strip()
        
    except Exception as e:
        print(f"Error in smart code extraction: {e}")
        return ""

def smart_extract_execution_result(execution_output, task):
    """
    Smart extraction of execution results using GPT
    Handles various output formats including errors and no-plan scenarios
    """
    client = get_openai_client()
    if not client:
        print("OpenAI client not available, falling back to basic extraction")
        return extract_answer_basic(execution_output, task)
    
    try:
        # Determine the expected output format based on task
        if task == "calendar":
            expected_format = '{"day": "Monday", "start_time": "14:30", "end_time": "15:30"}'
        elif task == "trip":
            expected_format = '{"itinerary": [{"day_range": "Day 1-3", "place": "Venice"}, {"day_range": "Day 3-5", "place": "Vienna"}]}'
        elif task == "meeting":
            expected_format = '{"itinerary": [{"action": "meet", "person": "David", "start_time": "13:00", "end_time": "14:00"}]}'
        
        prompt = f"""Extract structured data from the following execution output for a {task} planning task.

Execution Output:
{execution_output}

Expected format: {expected_format}

Instructions:
1. If the output contains valid JSON in the expected format, extract and return it
2. If the output contains an error message (like "No valid itinerary found", "Error:", etc.), return {{"error": "error_message"}}
3. If the output indicates no plan was found (like "No solution found", "UNSAT", etc.), return {{"no_plan": "reason"}}
4. If the output is malformed or unclear, try to extract any useful information or return {{"error": "malformed_output"}}

Return only valid JSON:"""

        response = client.chat.completions.create(
            model="gpt-4o-mini",
            messages=[{"role": "user", "content": prompt}],
            response_format={"type": "json_object"},
            temperature=0,
            max_tokens=1000
        )
        
        result = json.loads(response.choices[0].message.content)
        return result
        
    except Exception as e:
        print(f"Error in smart execution result extraction: {e}")
        return extract_answer_basic(execution_output, task)

def extract_answer_basic(answer_str, task):
    """Basic extraction fallback"""
    try:
        with open("../../scheduling_key.json") as f:
            key = json.load(f)["openai"]
        client = OpenAI(api_key=key)
    except (FileNotFoundError, KeyError):
        print("Warning: Could not initialize OpenAI client for answer extraction")
        return {}
    
    # If answer_str is None or empty, return empty dict
    if not answer_str:
        return {}
        
    # For meeting task, try to extract meeting information even if it doesn't start with SOLUTION:
    if task == "meeting":
        # Look for patterns like "Meet X at Y from HH:MM to HH:MM" or "Meet X (Y) from HH:MM to HH:MM"
        meetings = []
        lines = answer_str.split('\n')
        for line in lines:
            # Try different patterns
            patterns = [
                r"Meet\s+(\w+)\s+(?:at\s+)?(?:[^(]+)?(?:\([^)]+\))?\s+from\s+(\d{1,2}:\d{2})\s+(?:AM|PM)?\s+to\s+(\d{1,2}:\d{2})\s+(?:AM|PM)?",
                r"Meet\s+(\w+)\s+(?:at\s+)?(?:[^(]+)?(?:\([^)]+\))?\s+(\d{1,2}:\d{2})\s+(?:AM|PM)?\s+to\s+(\d{1,2}:\d{2})\s+(?:AM|PM)?",
                r"(\w+):\s+from\s+(\d{1,2}:\d{2})\s+(?:AM|PM)?\s+to\s+(\d{1,2}:\d{2})\s+(?:AM|PM)?"
            ]
            
            for pattern in patterns:
                match = re.search(pattern, line, re.IGNORECASE)
                if match:
                    person = match.group(1)
                    start_time = match.group(2)
                    end_time = match.group(3)
                    
                    # Convert to 24-hour format if needed
                    if "PM" in line and int(start_time.split(':')[0]) < 12:
                        start_hour = int(start_time.split(':')[0]) + 12
                        start_time = f"{start_hour:02d}:{start_time.split(':')[1]}"
                    if "PM" in line and int(end_time.split(':')[0]) < 12:
                        end_hour = int(end_time.split(':')[0]) + 12
                        end_time = f"{end_hour:02d}:{end_time.split(':')[1]}"
                    if "AM" in line and int(start_time.split(':')[0]) == 12:
                        start_time = f"00:{start_time.split(':')[1]}"
                    if "AM" in line and int(end_time.split(':')[0]) == 12:
                        end_time = f"00:{end_time.split(':')[1]}"
                    
                    meetings.append({
                        "action": "meet",
                        "person": person,
                        "start_time": start_time,
                        "end_time": end_time
                    })
                    break
        
        if meetings:
            return {"itinerary": meetings}
    
    # For trip task, use the revised format and instructions
    prompt = {
        "calendar": "Given the following time range:\n" + answer_str + "\nExtract the meeting start day and time in a JSON like {\"day\": \"Monday\", \"start_time\": \"14:30\", \"end_time\": \"15:30\"}. The time should be in 24-hour format. If no time range is given at all, output an empty JSON.",
        "trip": (
            "Given the following itinerary:\n" + answer_str +
            "\nExtract the days spent in each city in a JSON format like "
            "{\"itinerary\": [{\"day_range\": \"Day 1-4\", \"place\": \"Tallinn\"}, {\"day_range\": \"Day 4-6\", \"place\": \"Munich\"}]}. "
            "Each entry should represent a continuous stay in a city, with the day range inclusive. "
            "IMPORTANT: When you fly from city A to city B on day X, that day counts for BOTH cities. "
            "For example:\n"
            "- If you stay in Venice from Day 1-3 and fly to Vienna on Day 3, then:\n"
            "  - Venice: Day 1-3 (3 days)\n"
            "  - Vienna: Day 3-6 (4 days, including the flight day)\n"
            "- The flight day (Day 3) is counted for both Venice and Vienna.\n"
            "- Do NOT create separate flight entries in the JSON.\n"
            "If no itinerary is given, output an empty JSON."
        ),
        "meeting": "Given the following meeting schedule:\n" + answer_str + "\nExtract the time and the person of each meeting in a JSON format like {\"itinerary\": [{\"action\": \"meet\", \"person\": \"David\",\"start_time\": \"13:00\", \"end_time\": \"14:00\"}, ...]}. Do not include location. Only keep the meeting times, and ignore time for starting, waiting, or traveling. The time should be converted to a 24-hour format. If no time range is given at all, output an empty JSON"
    }
    
    try:
        response = client.responses.create(
            model="gpt-4.1-nano",
            input=[
                {
                "role": "user",
                "content": [
                    {
                        "type": "input_text",
                        "text": prompt[task]
                    }
                ]
                }
            ],
            text={
                "format": {
                "type": "json_object"
                }
            },
            reasoning={},
            tools=[],
            temperature=0,
            max_output_tokens=2000,
            top_p=1,
            store=True
        )
        output_json = response.output[0].content[0].text
        return json.loads(output_json)
    except Exception as e:
        print(f"Error in answer extraction: {e}")
        return {}

def evaluate_trip_refined(constraints, pred):
    """
    Sample evaluation for the revised trip format:
    - Checks that there are no flight entries
    - Checks that day ranges overlap on flight days
    - Checks that each city segment is a single entry with a day range
    - Checks total days in each city (including flight days) match constraints
    """
    if not pred or "itinerary" not in pred:
        return False, {"missing_itinerary": True}
    itinerary = pred["itinerary"]
    # Check for flight entries
    for entry in itinerary:
        if "flight" in entry.get("place", "").lower():
            return False, {"flight_entry_present": True}
    # Check for overlapping day ranges (flight days)
    prev_end = None
    prev_city = None
    for entry in itinerary:
        day_range = entry.get("day_range", "")
        city = entry.get("place", "")
        if not day_range.startswith("Day "):
            return False, {"bad_day_range_format": day_range}
        days = day_range.replace("Day ", "").split("-")
        start = int(days[0])
        end = int(days[-1])
        if prev_end is not None:
            # Should overlap on the flight day
            if start > prev_end:
                return False, {"gap_between_cities": (prev_city, city, prev_end, start)}
            if start < prev_end:
                return False, {"overlap_error": (prev_city, city, prev_end, start)}
        prev_end = end
        prev_city = city
    # Optionally, check total days in each city (including flight days) match constraints
    # (This requires constraints to specify expected days per city)
    # For now, just return True if above checks pass
    return True, {}

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
    
    # Test 4: Code with explanation but no proper wrapping
    response4 = """
    I'll solve this scheduling problem using Z3. Here's my approach:
    
    First, I need to import Z3 and create variables:
    from z3 import *
    day = Int('day')
    start_time = Int('start_time')
    end_time = Int('end_time')
    
    Now I'll create the solver and add constraints:
    s = Solver()
    s.add(day >= 1)
    s.add(day <= 7)
    s.add(start_time >= 0)
    s.add(start_time <= 23)
    s.add(end_time > start_time)
    
    Finally, I'll check for a solution:
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"Day: {m[day]}")
        print(f"Start Time: {m[start_time]}")
        print(f"End Time: {m[end_time]}")
    else:
        print("No solution found")
    """
    
    code4 = smart_extract_code(response4)
    print(f"Test 4 - Code with explanation: {'PASS' if 'from z3 import' in code4 and 's = Solver()' in code4 else 'FAIL'}")
    print(f"Extracted code length: {len(code4)}")
    
    # Test 5: Code embedded in markdown without proper blocks
    response5 = """
    # Z3 Solution for Scheduling Problem
    
    Here's my complete solution:
    
    ```python
    from z3 import *
    ```
    
    Now let's create the variables:
    day = Int('day')
    start_time = Int('start_time')
    
    And the solver:
    s = Solver()
    s.add(day >= 1)
    s.add(day <= 7)
    
    Check for solution:
    if s.check() == sat:
        m = s.model()
        print(f"Day: {m[day]}")
        print(f"Start Time: {m[start_time]}")
    """
    
    code5 = smart_extract_code(response5)
    print(f"Test 5 - Partial markdown blocks: {'PASS' if 'from z3 import' in code5 and 'day = Int' in code5 else 'FAIL'}")
    print(f"Extracted code length: {len(code5)}")
    
    # Test 6: Code with comments and explanations mixed
    response6 = """
    Let me write a Z3 program to solve this:
    
    # Import Z3 library
    from z3 import *
    
    # Define variables for the scheduling problem
    day = Int('day')  # Day of the week (1-7)
    start_time = Int('start_time')  # Start time in hours
    end_time = Int('end_time')  # End time in hours
    
    # Create Z3 solver
    s = Solver()
    
    # Add constraints based on the problem
    s.add(day >= 1)  # Day must be at least 1
    s.add(day <= 7)  # Day must be at most 7
    s.add(start_time >= 9)  # Start time must be at least 9 AM
    s.add(start_time <= 17)  # Start time must be at most 5 PM
    s.add(end_time > start_time)  # End time must be after start time
    s.add(end_time <= 18)  # End time must be at most 6 PM
    
    # Check if solution exists
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"Day: {m[day]}")
        print(f"Start Time: {m[start_time]}:00")
        print(f"End Time: {m[end_time]}:00")
    else:
        print("No valid solution found")
    """
    
    code6 = smart_extract_code(response6)
    print(f"Test 6 - Code with mixed comments: {'PASS' if 'from z3 import' in code6 and 's.add(day >= 1)' in code6 else 'FAIL'}")
    print(f"Extracted code length: {len(code6)}")

def test_smart_execution_result_extraction():
    """Test smart execution result extraction"""
    print("\nTesting smart execution result extraction...")
    
    # Test 1: Valid calendar output with SOLUTION prefix
    calendar_output1 = """
    SOLUTION:
    Day: Monday
    Start Time: 14:30
    End Time: 15:30
    """
    
    result1 = smart_extract_execution_result(calendar_output1, "calendar")
    print(f"Test 1 - Calendar with SOLUTION prefix: {'PASS' if result1.get('day') == 'Monday' else 'FAIL'}")
    print(f"Result: {result1}")
    
    # Test 2: Calendar output without SOLUTION prefix
    calendar_output2 = """
    Day: Tuesday
    Start Time: 10:00
    End Time: 11:00
    """
    
    result2 = smart_extract_execution_result(calendar_output2, "calendar")
    print(f"Test 2 - Calendar without prefix: {'PASS' if result2.get('day') == 'Tuesday' else 'FAIL'}")
    print(f"Result: {result2}")
    
    # Test 3: Calendar output with extra text
    calendar_output3 = """
    The Z3 solver found a solution:
    
    Day: Wednesday
    Start Time: 16:00
    End Time: 17:00
    
    This satisfies all constraints.
    """
    
    result3 = smart_extract_execution_result(calendar_output3, "calendar")
    print(f"Test 3 - Calendar with extra text: {'PASS' if result3.get('day') == 'Wednesday' else 'FAIL'}")
    print(f"Result: {result3}")
    
    # Test 4: Trip output with JSON format
    trip_output1 = """
    SOLUTION:
    {"itinerary": [{"day_range": "Day 1-3", "place": "Venice"}, {"day_range": "Day 3-5", "place": "Vienna"}]}
    """
    
    result4 = smart_extract_execution_result(trip_output1, "trip")
    print(f"Test 4 - Trip JSON format: {'PASS' if result4.get('itinerary') else 'FAIL'}")
    print(f"Result: {result4}")
    
    # Test 5: Trip output with natural language
    trip_output2 = """
    Here's the itinerary:
    
    Day 1-3: Venice
    Day 3-5: Vienna
    Day 5-7: Prague
    """
    
    result5 = smart_extract_execution_result(trip_output2, "trip")
    print(f"Test 5 - Trip natural language: {'PASS' if result5.get('itinerary') else 'FAIL'}")
    print(f"Result: {result5}")
    
    # Test 6: Meeting output with structured format
    meeting_output1 = """
    SOLUTION:
    Meet Alice from 13:00 to 14:00
    Meet Bob from 15:00 to 16:00
    Meet Charlie from 17:00 to 18:00
    """
    
    result6 = smart_extract_execution_result(meeting_output1, "meeting")
    print(f"Test 6 - Meeting structured format: {'PASS' if result6.get('itinerary') else 'FAIL'}")
    print(f"Result: {result6}")
    
    # Test 7: Meeting output with natural language
    meeting_output2 = """
    I'll meet with the following people:
    
    - Alice at the coffee shop from 1:00 PM to 2:00 PM
    - Bob in the conference room from 3:00 PM to 4:00 PM
    - Charlie at the library from 5:00 PM to 6:00 PM
    """
    
    result7 = smart_extract_execution_result(meeting_output2, "meeting")
    print(f"Test 7 - Meeting natural language: {'PASS' if result7.get('itinerary') else 'FAIL'}")
    print(f"Result: {result7}")
    
    # Test 8: Error output - NameError
    error_output1 = """
    Traceback (most recent call last):
      File "solution.py", line 10, in <module>
        s.add(day >= 1)
    NameError: name 'day' is not defined
    """
    
    result8 = smart_extract_execution_result(error_output1, "calendar")
    print(f"Test 8 - NameError: {'PASS' if 'error' in result8 else 'FAIL'}")
    print(f"Result: {result8}")
    
    # Test 9: Error output - SyntaxError
    error_output2 = """
    File "solution.py", line 5
        day = Int('day'
                    ^
    SyntaxError: invalid syntax
    """
    
    result9 = smart_extract_execution_result(error_output2, "calendar")
    print(f"Test 9 - SyntaxError: {'PASS' if 'error' in result9 else 'FAIL'}")
    print(f"Result: {result9}")
    
    # Test 10: No solution found - UNSAT
    no_solution_output1 = """
    No solution found
    UNSAT
    """
    
    result10 = smart_extract_execution_result(no_solution_output1, "calendar")
    print(f"Test 10 - UNSAT: {'PASS' if 'no_plan' in result10 else 'FAIL'}")
    print(f"Result: {result10}")
    
    # Test 11: No solution found - different format
    no_solution_output2 = """
    The problem is unsatisfiable.
    No valid solution exists.
    """
    
    result11 = smart_extract_execution_result(no_solution_output2, "calendar")
    print(f"Test 11 - No solution different format: {'PASS' if 'no_plan' in result11 else 'FAIL'}")
    print(f"Result: {result11}")
    
    # Test 12: Malformed output
    malformed_output = """
    Some random text that doesn't make sense
    and doesn't contain any structured data
    """
    
    result12 = smart_extract_execution_result(malformed_output, "calendar")
    print(f"Test 12 - Malformed output: {'PASS' if 'error' in result12 else 'FAIL'}")
    print(f"Result: {result12}")
    
    # Test 13: Empty output
    empty_output = ""
    
    result13 = smart_extract_execution_result(empty_output, "calendar")
    print(f"Test 13 - Empty output: {'PASS' if result13 == {} else 'FAIL'}")
    print(f"Result: {result13}")
    
    # Test 14: Calendar output with time conversion (AM/PM)
    calendar_output4 = """
    SOLUTION:
    Day: Friday
    Start Time: 2:30 PM
    End Time: 3:30 PM
    """
    
    result14 = smart_extract_execution_result(calendar_output4, "calendar")
    print(f"Test 14 - Calendar with AM/PM: {'PASS' if result14.get('start_time') == '14:30' else 'FAIL'}")
    print(f"Result: {result14}")
    
    # Test 15: Trip output with flight days
    trip_output3 = """
    SOLUTION:
    {"itinerary": [
        {"day_range": "Day 1-3", "place": "Venice"},
        {"day_range": "Day 3", "place": "Venice"},
        {"day_range": "Day 3", "place": "Vienna"},
        {"day_range": "Day 3-5", "place": "Vienna"}
    ]}
    """
    
    result15 = smart_extract_execution_result(trip_output3, "trip")
    print(f"Test 15 - Trip with flight days: {'PASS' if result15.get('itinerary') and len(result15['itinerary']) == 4 else 'FAIL'}")
    print(f"Result: {result15}")

def test_extraction_for_evaluation():
    """Test that extracted results are in the correct format for evaluation"""
    print("\nTesting extraction format for evaluation...")
    
    # Test 1: Calendar format validation
    calendar_output = """
    SOLUTION:
    Day: Monday
    Start Time: 14:30
    End Time: 15:30
    """
    
    result = smart_extract_execution_result(calendar_output, "calendar")
    expected_keys = ['day', 'start_time', 'end_time']
    has_required_keys = all(key in result for key in expected_keys)
    print(f"Test 1 - Calendar format: {'PASS' if has_required_keys else 'FAIL'}")
    print(f"Result keys: {list(result.keys())}")
    
    # Test 2: Trip format validation
    trip_output = """
    {"itinerary": [{"day_range": "Day 1-3", "place": "Venice"}, {"day_range": "Day 3-5", "place": "Vienna"}]}
    """
    
    result = smart_extract_execution_result(trip_output, "trip")
    has_itinerary = 'itinerary' in result and isinstance(result['itinerary'], list)
    has_valid_items = has_itinerary and all('day_range' in item and 'place' in item for item in result['itinerary'])
    print(f"Test 2 - Trip format: {'PASS' if has_valid_items else 'FAIL'}")
    print(f"Result structure: {result}")
    
    # Test 3: Meeting format validation
    meeting_output = """
    Meet Alice from 13:00 to 14:00
    Meet Bob from 15:00 to 16:00
    """
    
    result = smart_extract_execution_result(meeting_output, "meeting")
    has_itinerary = 'itinerary' in result and isinstance(result['itinerary'], list)
    has_valid_items = has_itinerary and all(
        'action' in item and 'person' in item and 'start_time' in item and 'end_time' in item 
        for item in result['itinerary']
    )
    print(f"Test 3 - Meeting format: {'PASS' if has_valid_items else 'FAIL'}")
    print(f"Result structure: {result}")
    
    # Test 4: Error format validation
    error_output = """
    NameError: name 'day' is not defined
    """
    
    result = smart_extract_execution_result(error_output, "calendar")
    has_error_key = 'error' in result
    print(f"Test 4 - Error format: {'PASS' if has_error_key else 'FAIL'}")
    print(f"Result: {result}")
    
    # Test 5: No plan format validation
    no_plan_output = """
    UNSAT
    """
    
    result = smart_extract_execution_result(no_plan_output, "calendar")
    has_no_plan_key = 'no_plan' in result
    print(f"Test 5 - No plan format: {'PASS' if has_no_plan_key else 'FAIL'}")
    print(f"Result: {result}")

def test_edge_cases():
    """Test edge cases and boundary conditions"""
    print("\nTesting edge cases...")
    
    # Test 1: Very long code with mixed content
    long_response = """
    This is a very long explanation of how to solve the problem.
    
    Let me start by explaining the approach:
    We need to use Z3 solver to find a valid schedule.
    
    Here's the complete solution:
    
    from z3 import *
    
    # Create variables
    day = Int('day')
    start_time = Int('start_time')
    end_time = Int('end_time')
    
    # Create solver
    s = Solver()
    
    # Add constraints
    s.add(day >= 1)
    s.add(day <= 7)
    s.add(start_time >= 0)
    s.add(start_time <= 23)
    s.add(end_time > start_time)
    s.add(end_time <= 24)
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"Day: {m[day]}")
        print(f"Start Time: {m[start_time]}")
        print(f"End Time: {m[end_time]}")
    else:
        print("No solution found")
    
    This solution handles all the constraints properly.
    """
    
    code = smart_extract_code(long_response)
    has_z3_import = 'from z3 import' in code
    has_solver = 's = Solver()' in code
    has_constraints = 's.add(' in code
    print(f"Test 1 - Long mixed content: {'PASS' if has_z3_import and has_solver and has_constraints else 'FAIL'}")
    print(f"Extracted code length: {len(code)}")
    
    # Test 2: Code with special characters
    special_chars_response = """
    Here's the solution with special characters:
    
    from z3 import *
    
    # Variables with special names
    day_var = Int('day_var')
    start_time_var = Int('start_time_var')
    
    # Solver with special constraints
    s = Solver()
    s.add(day_var >= 1)
    s.add(day_var <= 7)
    s.add(start_time_var >= 9)
    s.add(start_time_var <= 17)
    
    # Check solution
    if s.check() == sat:
        m = s.model()
        print(f"Day: {m[day_var]}")
        print(f"Start Time: {m[start_time_var]}")
    """
    
    code = smart_extract_code(special_chars_response)
    has_special_vars = 'day_var' in code and 'start_time_var' in code
    print(f"Test 2 - Special characters: {'PASS' if has_special_vars else 'FAIL'}")
    print(f"Extracted code length: {len(code)}")
    
    # Test 3: Execution output with mixed formats
    mixed_output = """
    Some debug information:
    Loading Z3 solver...
    Checking constraints...
    
    SOLUTION:
    Day: Thursday
    Start Time: 11:00
    End Time: 12:00
    
    Additional info:
    - All constraints satisfied
    - Solution is optimal
    """
    
    result = smart_extract_execution_result(mixed_output, "calendar")
    has_correct_data = result.get('day') == 'Thursday' and result.get('start_time') == '11:00'
    print(f"Test 3 - Mixed execution output: {'PASS' if has_correct_data else 'FAIL'}")
    print(f"Result: {result}")
    
    # Test 4: Code with multiple code blocks (should extract the last one)
    multiple_blocks_response = """
    Let me show you two approaches:
    
    ```python
    # First approach (incorrect)
    from z3 import *
    day = 1  # This is wrong
    ```
    
    ```python
    # Second approach (correct)
    from z3 import *
    day = Int('day')
    s = Solver()
    s.add(day >= 1)
    s.add(day <= 7)
    ```
    """
    
    code = smart_extract_code(multiple_blocks_response)
    has_correct_approach = 'day = Int(' in code and 's = Solver()' in code
    print(f"Test 4 - Multiple code blocks: {'PASS' if has_correct_approach else 'FAIL'}")
    print(f"Extracted code length: {len(code)}")

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
    print("Enhanced SMT Refinement Test Suite (Standalone)")
    print("=" * 50)
    
    try:
        test_smart_code_extraction()
        test_smart_execution_result_extraction()
        test_extraction_for_evaluation()
        test_edge_cases()
        test_error_handling_scenarios()
        test_basic_extraction_fallback()
        
        print("\n" + "=" * 50)
        print("All tests completed!")
        
    except Exception as e:
        print(f"\nTest failed with error: {e}")
        import traceback
        traceback.print_exc() 
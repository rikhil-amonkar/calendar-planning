#!/usr/bin/env python3

import json
import re

def extract_answer_from_text(text, task):
    """Extract structured answer from text response"""
    import re
    
    # Handle None or empty input
    if text is None or text.strip() == "":
        return None
    
    if task == "calendar":
        print(f"DEBUG: Processing calendar text (first 200 chars): {text[:200]}...")
        
        # First try to extract JSON from the response
        json_pattern = r'```json\s*(\{.*?\})\s*```'
        json_match = re.search(json_pattern, text, re.DOTALL | re.IGNORECASE)
        if json_match:
            print("DEBUG: Found JSON in code blocks")
            try:
                json_str = json_match.group(1)
                result = json.loads(json_str)
                if "time_range" in result and "day" in result:
                    print(f"DEBUG: Successfully parsed JSON with time_range and day")
                    return result
            except json.JSONDecodeError as e:
                print(f"DEBUG: JSON decode error: {e}")
                pass
        
        # Try to find JSON without code blocks (use re.DOTALL)
        json_pattern2 = r'\{[^}]*"time_range"[^}]*"day"[^}]*\}'
        json_match2 = re.search(json_pattern2, text, re.DOTALL)
        if json_match2:
            print("DEBUG: Found JSON without code blocks")
            try:
                result = json.loads(json_match2.group(0))
                if "time_range" in result and "day" in result:
                    print(f"DEBUG: Successfully parsed JSON with time_range and day")
                    return result
            except json.JSONDecodeError as e:
                print(f"DEBUG: JSON decode error: {e}")
                pass
        
        # Fallback: extract the last {...} block and try to parse as JSON
        print("DEBUG: Trying fallback - extract last {...} block")
        try:
            last_open = text.rfind('{')
            last_close = text.rfind('}')
            if last_open != -1 and last_close > last_open:
                json_str = text[last_open:last_close+1]
                print(f"DEBUG: Extracted JSON string: {json_str}")
                result = json.loads(json_str)
                if "time_range" in result and "day" in result:
                    print(f"DEBUG: Successfully parsed JSON with time_range and day")
                    return result
        except Exception as e:
            print(f"DEBUG: Fallback JSON decode error: {e}")
            pass
        
        # Look for time range pattern in the format "Monday, 13:30 - 14:30"
        print("DEBUG: Trying time pattern matching")
        time_pattern = r'(Monday|Tuesday|Wednesday|Thursday|Friday|Saturday|Sunday),?\s*(\d{1,2}:\d{2})\s*-\s*(\d{1,2}:\d{2})'
        match = re.search(time_pattern, text, re.IGNORECASE)
        
        if match:
            day = match.group(1)
            start_time = match.group(2)
            end_time = match.group(3)
            
            # Convert to the expected format {HH:MM:HH:MM}
            time_range = f"{{{start_time}:{end_time}}}"
            
            print(f"DEBUG: Found time pattern: {day}, {start_time}-{end_time}")
            return {
                "day": day,
                "time_range": time_range
            }
        
        print("DEBUG: No valid calendar data found in any format")
        return None
    
    return None

def test_example_33():
    """Test the specific case that failed"""
    print("=== Testing Example 33 (Failed Case) ===")
    
    # This is the exact output from the model
    calendar_output = """The available free times for Lisa, Bobby, and Randy are compared to find a 30-minute slot where all are free, while respecting Bobby's preference to avoid meetings after 15:00.

- Lisa is free from 13:00 to 16:00.
- Bobby is free from 12:00 to 15:00 (and prefers no meetings after 15:00).
- Randy is free from 13:30 to 14:30.

The overlapping free period is from 13:30 to 14:30. Within this window, any 30-minute slot works. For example, 13:30 to 14:00 is chosen as it satisfies all constraints and preferences.

{
  "time_range": "{13:30:14:00}",
  "day": "Monday"
}"""
    
    print(f"Input length: {len(calendar_output)}")
    print(f"Input preview: {calendar_output[:100]}...")
    print(f"Input ends with: {calendar_output[-100:]}...")
    
    result = extract_answer_from_text(calendar_output, "calendar")
    print(f"Result: {result}")
    print(f"Success: {result is not None and 'time_range' in result and 'day' in result}")
    print("-" * 50)

def test_variations():
    """Test different variations of the problematic format"""
    print("\n=== Testing Variations ===")
    
    test_cases = [
        # Case 1: Original problematic format
        """The available free times for Lisa, Bobby, and Randy are compared to find a 30-minute slot where all are free, while respecting Bobby's preference to avoid meetings after 15:00.

- Lisa is free from 13:00 to 16:00.
- Bobby is free from 12:00 to 15:00 (and prefers no meetings after 15:00).
- Randy is free from 13:30 to 14:30.

The overlapping free period is from 13:30 to 14:30. Within this window, any 30-minute slot works. For example, 13:30 to 14:00 is chosen as it satisfies all constraints and preferences.

{
  "time_range": "{13:30:14:00}",
  "day": "Monday"
}""",
        
        # Case 2: Compact JSON
        """Based on the constraints, I recommend scheduling the meeting on Monday from 13:30 to 14:00.

{"time_range": "{13:30:14:00}", "day": "Monday"}""",
        
        # Case 3: JSON with extra whitespace
        """Here is the solution:

{ "time_range": "{13:30:14:00}", "day": "Monday" }""",
        
        # Case 4: Natural language only
        """Based on the schedules, the meeting should be scheduled on Monday from 13:30 to 14:00.""",
        
        # Case 5: Empty or invalid
        """I cannot find a suitable time for the meeting.""",
    ]
    
    for i, test_case in enumerate(test_cases, 1):
        print(f"\n--- Test Case {i} ---")
        print(f"Input length: {len(test_case)}")
        if test_case:
            print(f"Input preview: {test_case[:100]}...")
        else:
            print("Input: (empty)")
        
        result = extract_answer_from_text(test_case, "calendar")
        print(f"Result: {result}")
        print(f"Success: {result is not None and 'time_range' in result and 'day' in result}")
        print("-" * 50)

def main():
    """Run all tests"""
    print("Debugging Calendar Extraction Issues")
    print("=" * 60)
    
    test_example_33()
    test_variations()
    
    print("\n" + "=" * 60)
    print("Debug tests completed!")

if __name__ == "__main__":
    main() 
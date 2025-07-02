#!/usr/bin/env python3

import json
import re

def extract_answer_from_text(text, task):
    """Extract structured answer from text response"""
    import re
    
    # Handle None or empty input
    if text is None or text.strip() == "":
        return None
    
    if task == "trip":
        print(f"DEBUG: Processing trip text (first 200 chars): {text[:200]}...")
        
        # First try to extract JSON from the response (for model outputs)
        json_pattern = r'```json\s*(\{.*?\})\s*```'
        json_match = re.search(json_pattern, text, re.DOTALL | re.IGNORECASE)
        if json_match:
            print("DEBUG: Found JSON in code blocks")
            try:
                json_str = json_match.group(1)
                result = json.loads(json_str)
                if "itinerary" in result and isinstance(result["itinerary"], list):
                    print(f"DEBUG: Successfully parsed JSON with itinerary: {len(result['itinerary'])} items")
                    return result
                else:
                    print(f"DEBUG: JSON parsed but missing itinerary or invalid format: {result}")
            except json.JSONDecodeError as e:
                print(f"DEBUG: JSON decode error: {e}")
                pass
        
        # Try to find JSON without code blocks
        json_pattern2 = r'\{[^}]*"itinerary"[^}]*\[[^}]*\]'
        json_match2 = re.search(json_pattern2, text, re.DOTALL)
        if json_match2:
            print("DEBUG: Found JSON without code blocks")
            try:
                # Find the complete JSON object
                start_pos = text.rfind('{', 0, json_match2.start())
                if start_pos == -1:
                    start_pos = json_match2.start()
                
                # Find the matching closing brace
                brace_count = 0
                end_pos = start_pos
                for i in range(start_pos, len(text)):
                    if text[i] == '{':
                        brace_count += 1
                    elif text[i] == '}':
                        brace_count -= 1
                        if brace_count == 0:
                            end_pos = i + 1
                            break
                
                json_str = text[start_pos:end_pos]
                print(f"DEBUG: Extracted JSON string: {json_str[:200]}...")
                result = json.loads(json_str)
                if "itinerary" in result and isinstance(result["itinerary"], list):
                    print(f"DEBUG: Successfully parsed JSON with itinerary: {len(result['itinerary'])} items")
                    return result
                else:
                    print(f"DEBUG: JSON parsed but missing itinerary or invalid format: {result}")
            except json.JSONDecodeError as e:
                print(f"DEBUG: JSON decode error: {e}")
                pass
        
        # Fallback: Parse golden trip plan format (for gold text)
        print("DEBUG: Trying to parse as gold text format")
        import re
        
        itinerary = []
        
        for line in text.split('\n'):
            line = line.strip()
            if not line or not line.startswith('**Day'):
                continue
                
            day_match = re.search(r'Day (\d+)(?:-(\d+))?', line)
            if not day_match:
                continue
                
            start_day = int(day_match.group(1))
            end_day = int(day_match.group(2)) if day_match.group(2) else start_day
            day_range = f"Day {start_day}-{end_day}"
            
            place_match = re.search(r'(?:Arriving in|Visit|Stay in|at) ([^\s,.]+)', line, re.IGNORECASE)
            if place_match:
                itinerary.append({
                    "day_range": day_range,
                    "place": place_match.group(1)
                })
                print(f"DEBUG: Found itinerary item: {day_range} - {place_match.group(1)}")
        
        # Sort by day range start for consistent comparison
        itinerary.sort(key=lambda x: (
            int(x["day_range"].split()[1].split("-")[0]),
            x["place"]
        ))
        
        if itinerary:
            print(f"DEBUG: Successfully parsed gold text with {len(itinerary)} items")
            return {"itinerary": itinerary}
        
        print("DEBUG: No valid itinerary found in any format")
        return None
    
    return None

def test_example_500():
    """Test the specific case that failed"""
    print("=== Testing Example 500 (Failed Case) ===")
    
    # This is a simulated model output that might have caused the issue
    # The actual output from the model would be different, but let's test various formats
    
    test_cases = [
        # Case 1: Empty or invalid response
        "",
        
        # Case 2: Response without JSON
        "I cannot provide a valid trip plan at this time.",
        
        # Case 3: Malformed JSON
        '{"itinerary": [{"day_range": "Day 1-7", "place": "Hamburg"}, {"day_range": "Day 7-13", "place": "Split"}]',
        
        # Case 4: JSON with missing closing brace
        '{"itinerary": [{"day_range": "Day 1-7", "place": "Hamburg"}, {"day_range": "Day 7-13", "place": "Split"}]',
        
        # Case 5: JSON in code blocks but malformed
        '```json\n{"itinerary": [{"day_range": "Day 1-7", "place": "Hamburg"}\n```',
        
        # Case 6: Valid JSON in code blocks
        '''```json
{
  "itinerary": [
    {"day_range": "Day 1-7", "place": "Hamburg"},
    {"day_range": "Day 7-13", "place": "Split"},
    {"day_range": "Day 13-14", "place": "Lyon"},
    {"day_range": "Day 14-19", "place": "Munich"},
    {"day_range": "Day 19-20", "place": "Manchester"}
  ]
}
```''',
        
        # Case 7: Gold text format
        """Here is the trip plan for visiting the 5 European cities for 20 days:

**Day 1-7:** Arriving in Hamburg and visit Hamburg for 7 days.
**Day 7:** Fly from Hamburg to Split.
**Day 7-13:** Visit Split for 7 days.
**Day 13:** Fly from Split to Lyon.
**Day 13-14:** Visit Lyon for 2 days.
**Day 14:** Fly from Lyon to Munich.
**Day 14-19:** Visit Munich for 6 days.
**Day 19:** Fly from Munich to Manchester.
**Day 19-20:** Visit Manchester for 2 days.""",
        
        # Case 8: Mixed format (JSON followed by text)
        '''Here is my trip plan:

```json
{
  "itinerary": [
    {"day_range": "Day 1-7", "place": "Hamburg"},
    {"day_range": "Day 7-13", "place": "Split"}
  ]
}
```

This plan covers the required cities and days.''',
    ]
    
    for i, test_case in enumerate(test_cases, 1):
        print(f"\n--- Test Case {i} ---")
        print(f"Input length: {len(test_case)}")
        if test_case:
            print(f"Input preview: {test_case[:100]}...")
        else:
            print("Input: (empty)")
        
        result = extract_answer_from_text(test_case, "trip")
        print(f"Result: {result}")
        print(f"Success: {result is not None and 'itinerary' in result}")
        print("-" * 50)

def test_real_example():
    """Test with a real example from the data"""
    print("\n=== Testing Real Example ===")
    
    # Load the actual example 500
    try:
        with open("../data/trip_planning_100.json", "r") as f:
            data = json.load(f)
        
        example_500 = None
        for item in data:
            if item.get("id") == "trip_planning_example_500":
                example_500 = item
                break
        
        if example_500:
            print(f"Found example 500: {example_500['id']}")
            gold_text = example_500.get("gold", "")
            print(f"Gold text length: {len(gold_text)}")
            print(f"Gold text preview: {gold_text[:200]}...")
            
            result = extract_answer_from_text(gold_text, "trip")
            print(f"Extraction result: {result}")
            print(f"Success: {result is not None and 'itinerary' in result}")
        else:
            print("Example 500 not found in data")
            
    except Exception as e:
        print(f"Error loading data: {e}")

def main():
    """Run all tests"""
    print("Debugging Trip Extraction Issues")
    print("=" * 60)
    
    test_example_500()
    test_real_example()
    
    print("\n" + "=" * 60)
    print("Debug tests completed!")

if __name__ == "__main__":
    main() 
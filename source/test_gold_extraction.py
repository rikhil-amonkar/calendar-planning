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
        # First try to extract JSON from the response
        json_pattern = r'```json\s*(\{.*?\})\s*```'
        json_match = re.search(json_pattern, text, re.DOTALL | re.IGNORECASE)
        if json_match:
            try:
                json_str = json_match.group(1)
                result = json.loads(json_str)
                if "time_range" in result and "day" in result:
                    return result
            except json.JSONDecodeError:
                pass
        
        # Try to find JSON without code blocks
        json_pattern2 = r'\{[^}]*"time_range"[^}]*"day"[^}]*\}'
        json_match2 = re.search(json_pattern2, text)
        if json_match2:
            try:
                return json.loads(json_match2.group(0))
            except json.JSONDecodeError:
                pass
        
        # Look for time range pattern in the format "Monday, 13:30 - 14:30"
        time_pattern = r'(Monday|Tuesday|Wednesday|Thursday|Friday|Saturday|Sunday),?\s*(\d{1,2}:\d{2})\s*-\s*(\d{1,2}:\d{2})'
        match = re.search(time_pattern, text, re.IGNORECASE)
        
        if match:
            day = match.group(1)
            start_time = match.group(2)
            end_time = match.group(3)
            
            # Convert to the expected format {HH:MM:HH:MM}
            time_range = f"{{{start_time}:{end_time}}}"
            
            return {
                "day": day,
                "time_range": time_range
            }
        
        return None
    
    elif task == "meeting":
        # Use LLM-based extraction for meetings (following SMT/Python approach)
        import os
        
        # Try to get OpenAI API key
        openai_key = None
        try:
            # Try to load from scheduling_key.json
            with open("../../scheduling_key.json") as f:
                key_data = json.load(f)
                openai_key = key_data.get("openai")
        except (FileNotFoundError, KeyError):
            # Try environment variable
            openai_key = os.getenv("OPENAI_API_KEY")
        
        if not openai_key:
            print("Warning: Could not find OpenAI API key for answer extraction")
            return None
        
        try:
            from openai import OpenAI
            client = OpenAI(api_key=openai_key)
        except Exception as e:
            print(f"Warning: Could not initialize OpenAI client for answer extraction: {e}")
            return None
        
        # Define extraction prompt for meetings
        prompt = f"Given the following meeting schedule:\n{text}\nExtract the time and the person of each meeting in a JSON format like {{\"itinerary\": [{{\"action\": \"meet\", \"person\": \"David\",\"start_time\": \"13:00\", \"end_time\": \"14:00\"}}, ...]}}. Do not include location. Only keep the meeting times, and ignore time for starting, waiting, or traveling. The time should be converted to a 24-hour format. If no time range is given at all, output an empty JSON."
        
        try:
            response = client.chat.completions.create(
                model="gpt-4o-mini",  # Using gpt-4o-mini as fallback
                messages=[
                    {
                        "role": "user",
                        "content": prompt
                    }
                ],
                response_format={"type": "json_object"},
                temperature=0,
                max_tokens=2000,
                top_p=1
            )
            output_json = response.choices[0].message.content
            print(f"Extracted answer JSON: {output_json}")
            return json.loads(output_json)
        except Exception as e:
            print(f"Error in answer extraction: {e}")
            return None
    
    elif task == "trip":
        # First try to extract JSON from the response (for model outputs)
        json_pattern = r'```json\s*(\{.*?\})\s*```'
        json_match = re.search(json_pattern, text, re.DOTALL | re.IGNORECASE)
        if json_match:
            try:
                json_str = json_match.group(1)
                result = json.loads(json_str)
                if "itinerary" in result and isinstance(result["itinerary"], list):
                    return result
            except json.JSONDecodeError:
                pass
        
        # Try to find JSON without code blocks
        json_pattern2 = r'\{[^}]*"itinerary"[^}]*\[[^}]*\]'
        json_match2 = re.search(json_pattern2, text, re.DOTALL)
        if json_match2:
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
                result = json.loads(json_str)
                if "itinerary" in result and isinstance(result["itinerary"], list):
                    return result
            except json.JSONDecodeError:
                pass
        
        # Fallback: Parse golden trip plan format (for gold text)
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
        
        # Sort by day range start for consistent comparison
        itinerary.sort(key=lambda x: (
            int(x["day_range"].split()[1].split("-")[0]),
            x["place"]
        ))
        
        if itinerary:
            return {"itinerary": itinerary}
        
        return None
    
    return None

def test_calendar_gold_extraction():
    """Test calendar gold text extraction"""
    print("=== Testing Calendar Gold Extraction ===")
    
    # Test case 1: Standard format
    calendar_gold = "Here is the proposed time: Monday, 13:30 - 14:30"
    result = extract_answer_from_text(calendar_gold, "calendar")
    expected = {
        "day": "Monday",
        "time_range": "{13:30:14:30}"
    }
    
    print(f"Input: {calendar_gold}")
    print(f"Expected: {expected}")
    print(f"Result: {result}")
    print(f"Success: {result == expected}")
    print()
    
    # Test case 2: Different format
    calendar_gold2 = "Here is the proposed time: Tuesday, 9:00 - 10:00"
    result2 = extract_answer_from_text(calendar_gold2, "calendar")
    expected2 = {
        "day": "Tuesday", 
        "time_range": "{9:00:10:00}"
    }
    
    print(f"Input: {calendar_gold2}")
    print(f"Expected: {expected2}")
    print(f"Result: {result2}")
    print(f"Success: {result2 == expected2}")
    print()

def test_meeting_gold_extraction():
    """Test meeting gold text extraction"""
    print("=== Testing Meeting Gold Extraction ===")
    
    # Test case 1: Standard format
    meeting_gold = [
        "You meet Sarah for 105 minutes from 2:45PM to 4:30PM",
        "You meet John for 60 minutes from 10:00AM to 11:00AM"
    ]
    
    # Convert list to string format as it would appear in the data
    meeting_gold_text = "\n".join(meeting_gold)
    
    print(f"Input: {meeting_gold_text}")
    print("Note: Meeting extraction requires OpenAI API key")
    print("Skipping actual extraction test for meetings")
    print()

def test_trip_gold_extraction():
    """Test trip gold text extraction"""
    print("=== Testing Trip Gold Extraction ===")
    
    # Test case 1: Standard gold format
    trip_gold = """Here is the trip plan for visiting the 8 European cities for 21 days:

**Day 1-2:** Arriving in Reykjavik and visit Reykjavik for 2 days.
**Day 2:** Fly from Reykjavik to Stockholm.
**Day 2-4:** Visit Stockholm for 3 days.
**Day 4:** Fly from Stockholm to Tallinn.
**Day 4-8:** Visit Tallinn for 5 days.
**Day 8:** Fly from Tallinn to Oslo.
**Day 8-12:** Visit Oslo for 5 days.
**Day 12:** Fly from Oslo to Geneva.
**Day 12-13:** Visit Geneva for 2 days.
**Day 13:** Fly from Geneva to Split.
**Day 13-15:** Visit Split for 3 days.
**Day 15:** Fly from Split to Stuttgart.
**Day 15-19:** Visit Stuttgart for 5 days.
**Day 19:** Fly from Stuttgart to Porto.
**Day 19-21:** Visit Porto for 3 days."""
    
    result = extract_answer_from_text(trip_gold, "trip")
    expected = {
        "itinerary": [
            {"day_range": "Day 1-2", "place": "Reykjavik"},
            {"day_range": "Day 2-4", "place": "Stockholm"},
            {"day_range": "Day 4-8", "place": "Tallinn"},
            {"day_range": "Day 8-12", "place": "Oslo"},
            {"day_range": "Day 12-13", "place": "Geneva"},
            {"day_range": "Day 13-15", "place": "Split"},
            {"day_range": "Day 15-19", "place": "Stuttgart"},
            {"day_range": "Day 19-21", "place": "Porto"}
        ]
    }
    
    print(f"Input: {trip_gold[:100]}...")
    print(f"Expected: {expected}")
    print(f"Result: {result}")
    
    # Check if result matches expected structure
    success = False
    if result and "itinerary" in result:
        itinerary = result["itinerary"]
        if len(itinerary) == len(expected["itinerary"]):
            # Check each item
            success = True
            for i, item in enumerate(itinerary):
                if (item.get("day_range") != expected["itinerary"][i]["day_range"] or
                    item.get("place") != expected["itinerary"][i]["place"]):
                    success = False
                    break
    
    print(f"Success: {success}")
    print()
    
    # Test case 2: Different format
    trip_gold2 = """Here is the trip plan for visiting the 4 European cities for 20 days:

**Day 1-6:** Arriving in Athens and visit Athens for 6 days.
**Day 6:** Fly from Athens to Zurich.
**Day 6-11:** Visit Zurich for 6 days.
**Day 11:** Fly from Zurich to Valencia.
**Day 11-16:** Visit Valencia for 6 days.
**Day 16:** Fly from Valencia to Naples.
**Day 16-20:** Visit Naples for 5 days."""
    
    result2 = extract_answer_from_text(trip_gold2, "trip")
    expected2 = {
        "itinerary": [
            {"day_range": "Day 1-6", "place": "Athens"},
            {"day_range": "Day 6-11", "place": "Zurich"},
            {"day_range": "Day 11-16", "place": "Valencia"},
            {"day_range": "Day 16-20", "place": "Naples"}
        ]
    }
    
    print(f"Input: {trip_gold2[:100]}...")
    print(f"Expected: {expected2}")
    print(f"Result: {result2}")
    
    # Check if result matches expected structure
    success2 = False
    if result2 and "itinerary" in result2:
        itinerary2 = result2["itinerary"]
        if len(itinerary2) == len(expected2["itinerary"]):
            # Check each item
            success2 = True
            for i, item in enumerate(itinerary2):
                if (item.get("day_range") != expected2["itinerary"][i]["day_range"] or
                    item.get("place") != expected2["itinerary"][i]["place"]):
                    success2 = False
                    break
    
    print(f"Success: {success2}")
    print()

def test_edge_cases():
    """Test edge cases and error handling"""
    print("=== Testing Edge Cases ===")
    
    # Test empty input
    empty_result = extract_answer_from_text("", "calendar")
    print(f"Empty input (calendar): {empty_result}")
    print(f"Success: {empty_result is None}")
    print()
    
    # Test invalid format
    invalid_result = extract_answer_from_text("This is not a valid format", "calendar")
    print(f"Invalid format (calendar): {invalid_result}")
    print(f"Success: {invalid_result is None}")
    print()
    
    # Test None input
    none_result = extract_answer_from_text(None, "trip")
    print(f"None input (trip): {none_result}")
    print(f"Success: {none_result is None}")
    print()

def main():
    """Run all tests"""
    print("Testing Gold Field Extraction")
    print("=" * 50)
    print()
    
    test_calendar_gold_extraction()
    test_meeting_gold_extraction()
    test_trip_gold_extraction()
    test_edge_cases()
    
    print("=" * 50)
    print("Gold extraction tests completed!")

if __name__ == "__main__":
    main() 
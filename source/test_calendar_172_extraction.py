#!/usr/bin/env python3

import json
import re
from openai import OpenAI

def test_calendar_extraction():
    """Test extraction of calendar example 172 output"""
    
    # The actual output from example 172
    execution_output = """SOLUTION:
Day: Monday
Start Time: 14:00
End Time: 14:30
"""
    
    print("Testing calendar extraction for example 172...")
    print(f"Input:\n{execution_output}")
    
    # Test 1: Try the smart extraction function
    try:
        with open("../../scheduling_key.json") as f:
            key = json.load(f)["openai"]
        client = OpenAI(api_key=key)
        
        expected_format = '{"day": "Monday", "start_time": "14:30", "end_time": "15:30"}'
        
        prompt = f"""Extract structured data from the following execution output for a calendar planning task.

Execution Output:
{execution_output}

Expected format: {expected_format}

Instructions:
1. If the output contains valid JSON in the expected format, extract and return it
2. If the output indicates no plan was found (like "No valid itinerary found", "No solution found", "UNSAT", "unsat", etc.), return {{"no_plan": "reason"}}
3. If the output contains an execution error message (like "Error:", "Exception:", "Traceback:", etc.), return {{"error": "error_message"}}
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
        print(f"Smart extraction result: {result}")
        
        if "error" in result and result["error"] == "malformed_output":
            print("❌ Smart extraction incorrectly classified as malformed_output")
        elif "day" in result and "start_time" in result and "end_time" in result:
            print("✅ Smart extraction worked correctly")
        else:
            print(f"⚠️ Smart extraction returned unexpected format: {result}")
            
    except Exception as e:
        print(f"❌ Smart extraction failed: {e}")
    
    # Test 2: Try basic extraction function
    try:
        prompt = "Given the following time range:\n" + execution_output + "\nExtract the meeting start day and time in a JSON like {\"day\": \"Monday\", \"start_time\": \"14:30\", \"end_time\": \"15:30\"}. The time should be in 24-hour format. If no time range is given at all, output an empty JSON."
        
        response = client.responses.create(
            model="gpt-4.1-nano",
            input=[
                {
                "role": "user",
                "content": [
                    {
                        "type": "input_text",
                        "text": prompt
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
        result = json.loads(output_json)
        print(f"Basic extraction result: {result}")
        
        if "day" in result and "start_time" in result and "end_time" in result:
            print("✅ Basic extraction worked correctly")
        else:
            print(f"⚠️ Basic extraction returned unexpected format: {result}")
            
    except Exception as e:
        print(f"❌ Basic extraction failed: {e}")
    
    # Test 3: Manual regex extraction
    print("\nTesting manual regex extraction...")
    
    # Extract day
    day_match = re.search(r'Day:\s*(Monday|Tuesday|Wednesday|Thursday|Friday|Saturday|Sunday)', execution_output, re.IGNORECASE)
    day = day_match.group(1) if day_match else None
    
    # Extract start time
    start_match = re.search(r'Start Time:\s*(\d{1,2}:\d{2})', execution_output)
    start_time = start_match.group(1) if start_match else None
    
    # Extract end time
    end_match = re.search(r'End Time:\s*(\d{1,2}:\d{2})', execution_output)
    end_time = end_match.group(1) if end_match else None
    
    if day and start_time and end_time:
        result = {
            "day": day,
            "start_time": start_time,
            "end_time": end_time
        }
        print(f"✅ Manual regex extraction: {result}")
    else:
        print(f"❌ Manual regex extraction failed: day={day}, start_time={start_time}, end_time={end_time}")

if __name__ == "__main__":
    test_calendar_extraction() 
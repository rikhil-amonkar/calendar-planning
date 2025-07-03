#!/usr/bin/env python3

import json
import re

def extract_answer_from_text(text, task):
    """Extract structured answer from text response"""
    import re
    
    if task == "trip":
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

# Test with the actual model response
test_response = '''After analyzing the constraints and direct flight connections, a feasible trip plan that satisfies all requirements is as follows:

- Start in Reykjavik for the conference on Day 1-2.
- Fly to Stockholm on Day 2 to meet the friend between Day 2-4, staying for 3 days.
- Fly to Oslo on Day 4, staying for 5 days.
- Fly to Tallinn on Day 8, staying for 5 days.
- Fly back to Oslo on Day 12 (this day is counted for both Tallinn and Oslo, but Oslo has already been visited, so it's a transit point; however, to proceed, fly to Geneva on the same day).
- Fly to Geneva on Day 12, arriving on Day 12, and stay for 2 days.
- Fly to Split on Day 13, arriving on Day 13, and stay for 3 days.
- Fly to Stuttgart on Day 15, arriving on Day 15, and stay for 5 days.
- Fly to Porto on Day 19, arriving on Day 19, for the workshop on Day 19-21, staying for 3 days.

The day ranges account for the rule that the flight day is counted for both the departure and arrival city. For example:
- On Day 12, flying from Tallinn to Oslo and then to Geneva means Day 12 is counted for Tallinn (departure) and Geneva (arrival), with Oslo as a transit point not requiring a separate stay.
- Porto is scheduled for Day 19-21 to cover the workshop.
- Stockholm includes Day 2-4 to cover the meeting.

The direct flights used are:
- Reykjavik to Stockholm (Day 2)
- Stockholm to Oslo (Day 4)
- Oslo to Tallinn (Day 8)
- Tallinn to Oslo (Day 12, transit)
- Oslo to Geneva (Day 12)
- Geneva to Split (Day 13)
- Split to Stuttgart (Day 15)
- Stuttgart to Porto (Day 19)

All cities are visited with their specified stay durations, and the total days sum to 21 with flight days shared.

Output in the required JSON format:

{"itinerary": [{"day_range": "Day 1-2", "place": "Reykjavik"}, {"day_range": "Day 2-4", "place": "Stockholm"}, {"day_range": "Day 4-8", "place": "Oslo"}, {"day_range": "Day 8-12", "place": "Tallinn"}, {"day_range": "Day 12-13", "place": "Geneva"}, {"day_range": "Day 13-15", "place": "Split"}, {"day_range": "Day 15-19", "place": "Stuttgart"}, {"day_range": "Day 19-21", "place": "Porto"}]}'''

result = extract_answer_from_text(test_response, "trip")
print("Extraction result:")
print(json.dumps(result, indent=2))
print(f"Success: {result is not None}") 
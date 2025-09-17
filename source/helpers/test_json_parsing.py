import re
import json

# Test the execution output from the example
execution_output = "{'itinerary': [{'day_range': 'Day 1-4', 'place': 'Madrid'}, {'day_range': 'Day 4-10', 'place': 'Manchester'}, {'day_range': 'Day 10-11', 'place': 'Vienna'}, {'day_range': 'Day 11-15', 'place': 'Stuttgart'}, {'day_range': 'Day 4', 'place': 'Madrid'}, {'day_range': 'Day 4', 'place': 'Manchester'}, {'day_range': 'Day 10', 'place': 'Manchester'}, {'day_range': 'Day 10', 'place': 'Vienna'}, {'day_range': 'Day 11', 'place': 'Vienna'}, {'day_range': 'Day 11', 'place': 'Stuttgart'}]}\n"

print("Original execution output:")
print(execution_output)

# Test the regex pattern
json_match = re.search(r'\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\}', execution_output, re.DOTALL)
if json_match:
    print("\nRegex match found:")
    print(json_match.group())
    
    # Try to parse the JSON
    try:
        pred_formatted = json.loads(json_match.group())
        print("\nSuccessfully parsed JSON:")
        print(json.dumps(pred_formatted, indent=2))
        
        # Check for duplicates
        itinerary = pred_formatted.get("itinerary", [])
        print(f"\nNumber of segments: {len(itinerary)}")
        
        # Check for exact duplicates
        seen = set()
        duplicates = []
        for i, segment in enumerate(itinerary):
            segment_str = json.dumps(segment, sort_keys=True)
            if segment_str in seen:
                duplicates.append((i, segment))
            seen.add(segment_str)
        
        if duplicates:
            print(f"\nFound {len(duplicates)} duplicate segments:")
            for i, segment in duplicates:
                print(f"  Index {i}: {segment}")
        else:
            print("\nNo exact duplicates found")
            
    except json.JSONDecodeError as e:
        print(f"\nJSON decode error: {e}")
else:
    print("\nNo regex match found") 
import json

def main():
    segments = []
    
    segments.append({"place": "Helsinki", "start": 1, "end": 2})
    
    next_start = segments[-1]["end"]
    segments.append({"place": "Madrid", "start": next_start, "end": next_start + 4 - 1})
    
    next_start = segments[-1]["end"]
    segments.append({"place": "Budapest", "start": next_start, "end": next_start + 4 - 1})
    
    next_start = segments[-1]["end"]
    segments.append({"place": "Reykjavik", "start": next_start, "end": next_start + 2 - 1})
    
    segments.append({"place": "Warsaw", "start": 9, "end": 11})
    
    next_start = segments[-1]["end"]
    segments.append({"place": "Split", "start": next_start, "end": next_start + 4 - 1})
    
    itinerary_list = []
    for seg in segments:
        day_range_str = f"Day {seg['start']}-{seg['end']}"
        itinerary_list.append({
            "day_range": day_range_str,
            "place": seg['place']
        })
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()
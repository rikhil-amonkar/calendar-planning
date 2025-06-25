import json

def main():
    segments = [
        {"start": 1, "end": 6, "city": "Geneva"},
        {"start": 6, "end": 7, "city": "Split"},
        {"start": 7, "end": 9, "city": "Vilnius"},
        {"start": 9, "end": 10, "city": "Helsinki"},
        {"start": 10, "end": 12, "city": "Reykjavik"}
    ]
    
    itinerary_list = []
    for seg in segments:
        start = seg['start']
        end = seg['end']
        if start == end:
            day_range_str = f"Day {start}"
        else:
            day_range_str = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range_str, "place": seg['city']})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()
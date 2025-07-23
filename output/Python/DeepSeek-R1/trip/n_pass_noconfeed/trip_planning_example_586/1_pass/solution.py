import json

def main():
    connections = [
        ("Prague", "Lyon"),
        ("Prague", "Frankfurt"),
        ("Frankfurt", "Lyon"),
        ("Helsinki", "Naples"),
        ("Helsinki", "Frankfurt"),
        ("Naples", "Frankfurt"),
        ("Prague", "Helsinki")
    ]
    
    direct_flights = set()
    for a, b in connections:
        direct_flights.add((a, b))
        direct_flights.add((b, a))
    
    segments = [
        {"place": "Prague", "duration": 2},
        {"place": "Helsinki", "duration": 4},
        {"place": "Naples", "duration": 4},
        {"place": "Frankfurt", "duration": 3},
        {"place": "Lyon", "duration": 3}
    ]
    
    valid = True
    for i in range(len(segments) - 1):
        from_city = segments[i]["place"]
        to_city = segments[i+1]["place"]
        if (from_city, to_city) not in direct_flights:
            valid = False
            break
    
    itinerary = []
    current_day = 1
    for seg in segments:
        end_day = current_day + seg["duration"] - 1
        day_range_str = f"Day {current_day}-{end_day}"
        itinerary.append({
            "day_range": day_range_str,
            "place": seg["place"]
        })
        current_day = end_day
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()
import json

def main():
    # Initialize itinerary with fixed segments
    itinerary = [
        {"day_range": "Day 1-4", "place": "Reykjavik"},
        {"day_range": "Day 4-7", "place": "Stuttgart"},
        {"day_range": "Day 13-15", "place": "Munich"},
        {"day_range": "Day 19-22", "place": "Istanbul"}
    ]
    
    # Define other segments with their day ranges and validate flight connections
    other_segments = [
        {"day_range": (7, 11), "place": "Valencia"},
        {"day_range": (11, 13), "place": "Seville"},
        {"day_range": (15, 19), "place": "Geneva"},
        {"day_range": (22, 25), "place": "Vilnius"}
    ]
    
    # Check flight connections between consecutive segments
    prev_place = "Stuttgart"
    prev_end = 7
    valid = True
    flights = {
        "Stuttgart": ["Valencia", "Istanbul"],
        "Valencia": ["Seville", "Istanbul", "Geneva", "Munich"],
        "Seville": ["Munich"],
        "Munich": ["Geneva", "Istanbul"],
        "Geneva": ["Istanbul"],
        "Istanbul": ["Vilnius"]
    }
    
    for seg in other_segments:
        start = seg["day_range"][0]
        place = seg["place"]
        if start != prev_end:
            valid = False
            break
        if place not in flights.get(prev_place, []):
            valid = False
            break
        prev_place = place
        prev_end = seg["day_range"][1]
    
    if valid:
        # Add other segments to itinerary
        itinerary.insert(2, {"day_range": f"Day 7-11", "place": "Valencia"})
        itinerary.insert(3, {"day_range": f"Day 11-13", "place": "Seville"})
        itinerary.insert(5, {"day_range": f"Day 15-19", "place": "Geneva"})
        itinerary.append({"day_range": f"Day 22-25", "place": "Vilnius"})
    
    # Format day ranges correctly
    formatted = []
    for entry in itinerary:
        days = entry["day_range"].split('-')
        start_day = int(days[0].split()[1])
        end_day = int(days[1])
        if start_day == end_day:
            dr = f"Day {start_day}"
        else:
            dr = f"Day {start_day}-{end_day}"
        formatted.append({"day_range": dr, "place": entry["place"]})
    
    # Output as JSON
    print(json.dumps({"itinerary": formatted}))

if __name__ == "__main__":
    main()
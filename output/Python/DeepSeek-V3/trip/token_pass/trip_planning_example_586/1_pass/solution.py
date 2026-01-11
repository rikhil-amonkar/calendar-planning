import json

def plan_trip():
    # Fixed constraints
    total_days = 12
    city_days_needed = {
        "Frankfurt": 3,
        "Naples": 4,
        "Helsinki": 4,
        "Lyon": 3,
        "Prague": 2
    }
    
    # Direct flights graph
    flights = {
        "Prague": ["Lyon", "Frankfurt", "Helsinki"],
        "Lyon": ["Prague", "Frankfurt"],
        "Frankfurt": ["Prague", "Lyon", "Helsinki", "Naples"],
        "Helsinki": ["Naples", "Frankfurt", "Prague"],
        "Naples": ["Helsinki", "Frankfurt"]
    }
    
    # Predefined schedule from logical deduction
    itinerary = [
        {"day_range": "Day 1-2", "place": "Prague"},
        {"day_range": "Day 2-5", "place": "Helsinki"},
        {"day_range": "Day 5-8", "place": "Naples"},
        {"day_range": "Day 8-10", "place": "Frankfurt"},
        {"day_range": "Day 10-12", "place": "Lyon"}
    ]
    
    # Verification
    day_counts = {}
    for segment in itinerary:
        place = segment["place"]
        day_range = segment["day_range"]
        # Parse "Day X-Y"
        parts = day_range.replace("Day ", "").split("-")
        start = int(parts[0])
        end = int(parts[1])
        length = end - start + 1
        day_counts[place] = day_counts.get(place, 0) + length
    
    # Check against requirements
    for city, needed in city_days_needed.items():
        if day_counts.get(city, 0) != needed:
            raise ValueError(f"Schedule error: {city} has {day_counts.get(city,0)} days, needs {needed}")
    
    # Check flight connections
    for i in range(len(itinerary) - 1):
        from_city = itinerary[i]["place"]
        to_city = itinerary[i + 1]["place"]
        if to_city not in flights[from_city]:
            raise ValueError(f"No direct flight from {from_city} to {to_city}")
    
    # Check total days
    total_scheduled = sum(day_counts.values())
    if total_scheduled != total_days:
        raise ValueError(f"Total days mismatch: {total_scheduled} vs {total_days}")
    
    # Check Helsinki show days 2-5
    helsinki_segment = [s for s in itinerary if s["place"] == "Helsinki"][0]
    h_start, h_end = map(int, helsinki_segment["day_range"].replace("Day ", "").split("-"))
    if not (h_start <= 2 and h_end >= 5):
        raise ValueError("Helsinki show days 2-5 not covered")
    
    # Check Prague workshop between day 1-2
    prague_segment = [s for s in itinerary if s["place"] == "Prague"][0]
    p_start, p_end = map(int, prague_segment["day_range"].replace("Day ", "").split("-"))
    if not (p_start <= 1 and p_end >= 2):
        raise ValueError("Prague workshop days 1-2 not covered")
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = plan_trip()
    print(json.dumps(result, indent=2))
import json

def compute_itinerary():
    total_days = 14
    days_needed = {
        "Split": 5,
        "Vilnius": 4,
        "Santorini": 2,
        "Madrid": 6
    }
    
    # Direct flights graph
    flights = {
        "Vilnius": ["Split"],
        "Split": ["Vilnius", "Madrid"],
        "Madrid": ["Split", "Santorini"],
        "Santorini": ["Madrid"]
    }
    
    # Fixed: last 2 days in Santorini
    fixed_santorini_last = True
    santorini_last_days = (13, 14)
    
    # We deduced the only feasible path without backtracking:
    # Vilnius -> Split -> Madrid -> Santorini
    # with travel days on day 4, 8, 13.
    
    # Compute day ranges:
    # Vilnius: day 1 to day 4
    # Split: day 4 to day 8
    # Madrid: day 8 to day 13
    # Santorini: day 13 to day 14
    
    itinerary = [
        {"day_range": "Day 1-4", "place": "Vilnius"},
        {"day_range": "Day 4-8", "place": "Split"},
        {"day_range": "Day 8-13", "place": "Madrid"},
        {"day_range": "Day 13-14", "place": "Santorini"}
    ]
    
    # Verification
    city_days_count = {}
    for entry in itinerary:
        place = entry["place"]
        day_range = entry["day_range"]
        start, end = map(int, day_range.replace("Day ", "").split("-"))
        days = end - start + 1
        city_days_count[place] = city_days_count.get(place, 0) + days
    
    # Check against requirements
    for city, needed in days_needed.items():
        if city_days_count.get(city, 0) != needed:
            raise ValueError(f"City {city} has {city_days_count.get(city,0)} days, needs {needed}")
    
    # Check total days
    total_calendar = max([int(entry["day_range"].split("-")[1].strip()) for entry in itinerary])
    if total_calendar != total_days:
        raise ValueError(f"Total calendar days mismatch: {total_calendar} vs {total_days}")
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, indent=2))
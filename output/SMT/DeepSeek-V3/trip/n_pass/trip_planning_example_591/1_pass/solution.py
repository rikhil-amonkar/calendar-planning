import json

def generate_itinerary():
    itinerary = [
        {"day_range": "Day 1-4", "place": "Geneva"},
        {"day_range": "Day 4", "place": "Geneva"},
        {"day_range": "Day 4", "place": "Munich"},
        {"day_range": "Day 4-10", "place": "Munich"},
        {"day_range": "Day 10", "place": "Munich"},
        {"day_range": "Day 10", "place": "Bucharest"},
        {"day_range": "Day 10-11", "place": "Bucharest"},
        {"day_range": "Day 11", "place": "Bucharest"},
        {"day_range": "Day 11", "place": "Valencia"},
        {"day_range": "Day 11-16", "place": "Valencia"},
        {"day_range": "Day 16", "place": "Valencia"},
        {"day_range": "Day 16", "place": "Stuttgart"},
        {"day_range": "Day 16-17", "place": "Stuttgart"}
    ]
    return {"itinerary": itinerary}

result = generate_itinerary()
print(json.dumps(result, indent=2))
import json

def create_itinerary():
    itinerary = [
        {"day_range": "Day 1-3", "place": "Berlin"},
        {"day_range": "Day 3", "place": "Berlin"},
        {"day_range": "Day 3", "place": "Barcelona"},
        {"day_range": "Day 3-4", "place": "Barcelona"},
        {"day_range": "Day 4", "place": "Barcelona"},
        {"day_range": "Day 4", "place": "Lyon"},
        {"day_range": "Day 4-5", "place": "Lyon"},
        {"day_range": "Day 5", "place": "Lyon"},
        {"day_range": "Day 5", "place": "Nice"},
        {"day_range": "Day 5-9", "place": "Nice"},
        {"day_range": "Day 9", "place": "Nice"},
        {"day_range": "Day 9", "place": "Athens"},
        {"day_range": "Day 9-13", "place": "Athens"},
        {"day_range": "Day 13", "place": "Athens"},
        {"day_range": "Day 13", "place": "Vilnius"},
        {"day_range": "Day 13-16", "place": "Vilnius"},
        {"day_range": "Day 16", "place": "Vilnius"},
        {"day_range": "Day 16", "place": "Berlin"},
        {"day_range": "Day 16", "place": "Stockholm"},
        {"day_range": "Day 16-20", "place": "Stockholm"}
    ]
    return {"itinerary": itinerary}

# Generate the itinerary
result = create_itinerary()
print(json.dumps(result, indent=2))
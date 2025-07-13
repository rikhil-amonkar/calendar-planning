import json

def generate_itinerary():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Nice"},
        {"day_range": "Day 5", "place": "Nice"},
        {"day_range": "Day 5", "place": "Lyon"},
        {"day_range": "Day 5-8", "place": "Lyon"},
        {"day_range": "Day 8", "place": "Lyon"},
        {"day_range": "Day 8", "place": "Dublin"},
        {"day_range": "Day 8-14", "place": "Dublin"},
        {"day_range": "Day 14", "place": "Dublin"},
        {"day_range": "Day 14", "place": "Krakow"},
        {"day_range": "Day 14-19", "place": "Krakow"},
        {"day_range": "Day 19", "place": "Krakow"},
        {"day_range": "Day 19", "place": "Frankfurt"},
        {"day_range": "Day 19-20", "place": "Frankfurt"}
    ]
    return {"itinerary": itinerary}

# Generate and print the itinerary
result = generate_itinerary()
print(json.dumps(result, indent=2))
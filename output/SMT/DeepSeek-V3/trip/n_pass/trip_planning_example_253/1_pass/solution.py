import json

def generate_itinerary():
    itinerary = [
        {"day_range": "Day 1-7", "place": "Vienna"},
        {"day_range": "Day 7", "place": "Vienna"},
        {"day_range": "Day 7", "place": "Lyon"},
        {"day_range": "Day 7-9", "place": "Lyon"},
        {"day_range": "Day 9", "place": "Lyon"},
        {"day_range": "Day 9", "place": "Amsterdam"},
        {"day_range": "Day 9-11", "place": "Amsterdam"},
        {"day_range": "Day 11", "place": "Amsterdam"},
        {"day_range": "Day 11", "place": "Santorini"},
        {"day_range": "Day 11-14", "place": "Santorini"}
    ]
    return {"itinerary": itinerary}

# Generate and print the itinerary.
itinerary = generate_itinerary()
print(json.dumps(itinerary, indent=2))
import json

def create_itinerary():
    itinerary = {
        "itinerary": [
            {"day_range": "Day 1-4", "place": "Venice"},
            {"day_range": "Day 4", "place": "Venice"},
            {"day_range": "Day 4", "place": "Stuttgart"},
            {"day_range": "Day 4-7", "place": "Stuttgart"},
            {"day_range": "Day 7", "place": "Stuttgart"},
            {"day_range": "Day 7", "place": "Krakow"},
            {"day_range": "Day 7-11", "place": "Krakow"},
            {"day_range": "Day 11", "place": "Krakow"},
            {"day_range": "Day 11", "place": "Stuttgart"},
            {"day_range": "Day 11-13", "place": "Stuttgart"},
            {"day_range": "Day 13", "place": "Stuttgart"},
            {"day_range": "Day 13", "place": "Split"},
            {"day_range": "Day 13-15", "place": "Split"},
            {"day_range": "Day 15", "place": "Split"},
            {"day_range": "Day 15", "place": "Athens"},
            {"day_range": "Day 15-19", "place": "Athens"},
            {"day_range": "Day 19", "place": "Athens"},
            {"day_range": "Day 19", "place": "Mykonos"},
            {"day_range": "Day 19-20", "place": "Mykonos"}
        ]
    }
    return itinerary

print(json.dumps(create_itinerary(), indent=2))
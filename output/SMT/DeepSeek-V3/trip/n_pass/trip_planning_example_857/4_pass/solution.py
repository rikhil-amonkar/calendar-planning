import json

def get_itinerary():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Hamburg"},
        {"day_range": "Day 5", "place": "Hamburg"},
        {"day_range": "Day 5", "place": "Frankfurt"},
        {"day_range": "Day 5-6", "place": "Frankfurt"},
        {"day_range": "Day 6", "place": "Frankfurt"},
        {"day_range": "Day 6", "place": "Geneva"},
        {"day_range": "Day 6-9", "place": "Geneva"},
        {"day_range": "Day 9", "place": "Geneva"},
        {"day_range": "Day 9", "place": "Porto"},
        {"day_range": "Day 9-10", "place": "Porto"},
        {"day_range": "Day 10", "place": "Porto"},
        {"day_range": "Day 10", "place": "Mykonos"},
        {"day_range": "Day 10-13", "place": "Mykonos"},
        {"day_range": "Day 13", "place": "Mykonos"},
        {"day_range": "Day 13", "place": "Naples"},
        {"day_range": "Day 13-15", "place": "Naples"},
        {"day_range": "Day 15", "place": "Naples"},
        {"day_range": "Day 15", "place": "Manchester"},
        {"day_range": "Day 15-18", "place": "Manchester"}
    ]
    return {"itinerary": itinerary}

print(json.dumps(get_itinerary(), indent=2))
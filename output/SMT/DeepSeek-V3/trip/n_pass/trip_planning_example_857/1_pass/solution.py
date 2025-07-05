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
        {"day_range": "Day 9", "place": "Mykonos"},
        {"day_range": "Day 9-12", "place": "Mykonos"},
        {"day_range": "Day 12", "place": "Mykonos"},
        {"day_range": "Day 12", "place": "Naples"},
        {"day_range": "Day 12-14", "place": "Naples"},
        {"day_range": "Day 14", "place": "Naples"},
        {"day_range": "Day 14", "place": "Porto"},
        {"day_range": "Day 14-16", "place": "Porto"},
        {"day_range": "Day 16", "place": "Porto"},
        {"day_range": "Day 16", "place": "Manchester"},
        {"day_range": "Day 16-18", "place": "Manchester"}
    ]
    return {"itinerary": itinerary}

print(json.dumps(get_itinerary(), indent=2))
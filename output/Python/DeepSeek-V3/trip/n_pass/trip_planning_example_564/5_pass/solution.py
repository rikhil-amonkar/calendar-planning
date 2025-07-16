import json

def find_itinerary():
    return {
        "itinerary": [
            {"day_range": "Day 1-5", "place": "Naples"},      # 5 days (part of 7)
            {"day_range": "Day 6-9", "place": "Seville"},      # 4 days
            {"day_range": "Day 10-11", "place": "Istanbul"},   # 2 days (consecutive)
            {"day_range": "Day 12-14", "place": "Rome"},       # 3 days
            {"day_range": "Day 15-16", "place": "Naples"},     # 2 more days (total 7)
            {"day_range": "Day 10-13", "place": "Santorini"}   # 4 days (overlaps with Istanbul and Rome)
        ]
    }

print(json.dumps(find_itinerary()))
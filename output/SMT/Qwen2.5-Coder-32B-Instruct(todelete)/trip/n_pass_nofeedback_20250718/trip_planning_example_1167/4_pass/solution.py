import json

# Manually constructed itinerary
itinerary = [
    {"day": 1, "place": "Dublin"},
    {"day": 2, "place": "Dublin"},
    {"day": 3, "place": "Dublin"},
    {"day": 4, "place": "Dublin"},
    {"day": 5, "place": "Dublin"},
    {"day": 6, "place": "Brussels"},
    {"day": 7, "place": "Brussels"},
    {"day": 8, "place": "Krakow"},
    {"day": 9, "place": "Krakow"},
    {"day": 10, "place": "Krakow"},
    {"day": 11, "place": "Frankfurt"},
    {"day": 12, "place": "Frankfurt"},
    {"day": 13, "place": "Frankfurt"},
    {"day": 14, "place": "Mykonos"},
    {"day": 15, "place": "Mykonos"},
    {"day": 16, "place": "Mykonos"},
    {"day": 17, "place": "Naples"},
    {"day": 18, "place": "Naples"},
    {"day": 19, "place": "Naples"},
    {"day": 20, "place": "Venice"},
    {"day": 21, "place": "Venice"}
]

# Convert to JSON format
result = {"itinerary": itinerary}
print(json.dumps(result, indent=4))
# Manually constructed itinerary
itinerary = [
    {"day": 1, "city": "Lisbon"},
    {"day": 2, "city": "Lisbon"},
    {"day": 3, "city": "Valencia"},
    {"day": 4, "city": "Valencia"},
    {"day": 5, "city": "Seville"},
    {"day": 6, "city": "Seville"},
    {"day": 7, "city": "Seville"},
    {"day": 8, "city": "Seville"},
    {"day": 9, "city": "Seville"},
    {"day": 10, "city": "Lyon"},
    {"day": 11, "city": "Lyon"},
    {"day": 12, "city": "Lyon"},
    {"day": 13, "city": "Oslo"},
    {"day": 14, "city": "Oslo"},
    {"day": 15, "city": "Oslo"},
    {"day": 16, "city": "Prague"},
    {"day": 17, "city": "Prague"},
    {"day": 18, "city": "Prague"},
    {"day": 19, "city": "Paris"},
    {"day": 20, "city": "Paris"},
    {"day": 21, "city": "Mykonos"},
    {"day": 22, "city": "Mykonos"},
    {"day": 23, "city": "Mykonos"},
    {"day": 24, "city": "Mykonos"},
    {"day": 25, "city": "Mykonos"}
]

# Convert to JSON format
import json
itinerary_json = json.dumps({"itinerary": itinerary}, indent=2)
print(itinerary_json)
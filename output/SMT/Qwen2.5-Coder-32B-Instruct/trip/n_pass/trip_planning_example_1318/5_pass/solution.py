import json

# Define the final itinerary
itinerary = [
    {"day": 1, "city": "Geneva"},
    {"day": 2, "city": "Geneva"},
    {"day": 3, "city": "Geneva"},
    {"day": 4, "city": "Tallinn"},
    {"day": 5, "city": "Tallinn"},
    {"day": 6, "city": "Tallinn"},
    {"day": 7, "city": "Tallinn"},
    {"day": 8, "city": "Tallinn"},
    {"day": 9, "city": "Edinburgh"},
    {"day": 10, "city": "Edinburgh"},
    {"day": 11, "city": "Edinburgh"},
    {"day": 12, "city": "Budapest"},
    {"day": 13, "city": "Budapest"},
    {"day": 14, "city": "Budapest"},
    {"day": 15, "city": "Budapest"},
    {"day": 16, "city": "Budapest"},
    {"day": 17, "city": "Helsinki"},
    {"day": 18, "city": "Helsinki"},
    {"day": 19, "city": "Vilnius"},
    {"day": 20, "city": "Vilnius"},
    {"day": 21, "city": "Vilnius"},
    {"day": 22, "city": "Vilnius"},
    {"day": 23, "city": "Vilnius"},
    {"day": 24, "city": "Oslo"},
    {"day": 25, "city": "Oslo"}
]

# Output the itinerary in JSON format
print(json.dumps({"itinerary": itinerary}, indent=2))
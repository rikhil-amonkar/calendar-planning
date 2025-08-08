import json

# Manually constructed itinerary
itinerary = [
    {"day": 1, "place": "Manchester"},
    {"day": 2, "place": "Manchester"},
    {"day": 3, "place": "Manchester"},
    {"day": 4, "place": "Manchester"},
    {"day": 5, "place": "Manchester"},
    {"day": 6, "place": "Manchester"},
    {"day": 7, "place": "Manchester"},
    {"day": 8, "place": "Vienna"},
    {"day": 9, "place": "Vienna"},
    {"day": 10, "place": "Stuttgart"},
    {"day": 11, "place": "Stuttgart"},
    {"day": 12, "place": "Stuttgart"},
    {"day": 13, "place": "Stuttgart"},
    {"day": 14, "place": "Stuttgart"},
    {"day": 15, "place": "Stuttgart"},
    {"day": 16, "place": "Vienna"},
    {"day": 17, "place": "Vienna"},
    {"day": 18, "place": "Madrid"},
    {"day": 19, "place": "Madrid"},
    {"day": 20, "place": "Madrid"},
    {"day": 21, "place": "Madrid"}
]

# Ensure the itinerary is within 15 days
itinerary = [entry for entry in itinerary if entry["day"] <= 15]

# Print the itinerary in JSON format
print(json.dumps({"itinerary": itinerary}, indent=2))
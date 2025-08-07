import json

# Define the itinerary manually
itinerary = [
    {"day": 1, "place": "Prague"},
    {"day": 2, "place": "Prague"},
    {"day": 3, "place": "Helsinki"},
    {"day": 4, "place": "Helsinki"},
    {"day": 5, "place": "Helsinki"},
    {"day": 6, "place": "Helsinki"},
    {"day": 7, "place": "Frankfurt"},
    {"day": 8, "place": "Frankfurt"},
    {"day": 9, "place": "Frankfurt"},
    {"day": 10, "place": "Naples"},
    {"day": 11, "place": "Naples"},
    {"day": 12, "place": "Naples"}
]

# Print the final itinerary in JSON format
print(json.dumps({"itinerary": itinerary}, indent=2))
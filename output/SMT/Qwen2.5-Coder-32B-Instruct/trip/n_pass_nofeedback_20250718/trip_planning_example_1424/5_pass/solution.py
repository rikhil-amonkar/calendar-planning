import json

# Manually constructed feasible itinerary
itinerary = [
    {"day": 1, "city": "Porto"},
    {"day": 6, "city": "Amsterdam"},
    {"day": 10, "city": "Helsinki"},
    {"day": 14, "city": "Split"},
    {"day": 17, "city": "Naples"},
    {"day": 21, "city": "Brussels"},
    {"day": 24, "city": "Reykjavik"},
    {"day": 27, "city": "Warsaw"}
]

# Print the final itinerary in JSON format
print(json.dumps({"itinerary": itinerary}, indent=4))
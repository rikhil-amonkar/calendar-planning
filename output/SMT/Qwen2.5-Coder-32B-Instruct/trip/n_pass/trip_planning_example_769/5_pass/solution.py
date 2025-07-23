import json

# Define the itinerary
itinerary = [
    {"day": 1, "city": "Porto"},
    {"day": 2, "city": "Porto"},
    {"day": 3, "city": "Porto"},
    {"day": 4, "city": "Porto"},
    {"day": 5, "city": "Porto"},
    {"day": 6, "city": "Amsterdam"},
    {"day": 7, "city": "Munich"},
    {"day": 8, "city": "Munich"},
    {"day": 9, "city": "Munich"},
    {"day": 10, "city": "Munich"},
    {"day": 11, "city": "Prague"},
    {"day": 12, "city": "Prague"},
    {"day": 13, "city": "Prague"},
    {"day": 14, "city": "Prague"},
    {"day": 15, "city": "Amsterdam"},
    {"day": 16, "city": "Santorini"},
    {"day": 17, "city": "Santorini"}
]

# Print the itinerary in JSON format
print(json.dumps({"itinerary": itinerary}, indent=2))
import json

# Define the itinerary manually
itinerary = [
    {"day": 1, "city": "Porto"},
    {"day": 2, "city": "Porto"},
    {"day": 3, "city": "Porto"},
    {"day": 4, "city": "Munich"},
    {"day": 5, "city": "Munich"},
    {"day": 6, "city": "Munich"},
    {"day": 7, "city": "Munich"},
    {"day": 8, "city": "Munich"},
    {"day": 9, "city": "Florence"},
    {"day": 10, "city": "Florence"},
    {"day": 11, "city": "Florence"},
    {"day": 12, "city": "Vienna"},
    {"day": 13, "city": "Vienna"},
    {"day": 14, "city": "Warsaw"},
    {"day": 15, "city": "Warsaw"},
    {"day": 16, "city": "Warsaw"},
    {"day": 17, "city": "Nice"},
    {"day": 18, "city": "Nice"},
    {"day": 19, "city": "Nice"},
    {"day": 20, "city": "Nice"},
    {"day": 21, "city": "Paris"},
    {"day": 22, "city": "Paris"},
    {"day": 23, "city": "Paris"},
    {"day": 24, "city": "Paris"}
]

# Print the itinerary in JSON format
print(json.dumps({"itinerary": itinerary}, indent=2))
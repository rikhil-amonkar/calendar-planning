import json

# Define the itinerary manually
itinerary = [
    {"day_range": "Day 1-4", "place": "Madrid"},
    {"day_range": "Day 4", "place": "Madrid"},
    {"day_range": "Day 5", "place": "Porto"},
    {"day_range": "Day 5-7", "place": "Porto"},
    {"day_range": "Day 7", "place": "Porto"},
    {"day_range": "Day 7", "place": "Stuttgart"},
    {"day_range": "Day 7-13", "place": "Stuttgart"},
    {"day_range": "Day 13", "place": "Stuttgart"}
]

# Print the itinerary in JSON format
print(json.dumps({"itinerary": itinerary}, indent=2))
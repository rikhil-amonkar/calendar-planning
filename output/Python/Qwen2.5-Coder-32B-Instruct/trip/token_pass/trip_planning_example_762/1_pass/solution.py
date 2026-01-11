import json

# Define the itinerary based on the constraints and logical rules
itinerary = [
    {"day_range": "Day 1-2", "place": "Berlin"},
    {"day_range": "Day 3-7", "place": "Berlin"},
    {"day_range": "Day 8-9", "place": "Dublin"},
    {"day_range": "Day 10-11", "place": "London"},
    {"day_range": "Day 12-14", "place": "Oslo"},
    {"day_range": "Day 15", "place": "Vilnius"}
]

# Output the itinerary as a JSON-formatted dictionary
output = {"itinerary": itinerary}
print(json.dumps(output, indent=4))
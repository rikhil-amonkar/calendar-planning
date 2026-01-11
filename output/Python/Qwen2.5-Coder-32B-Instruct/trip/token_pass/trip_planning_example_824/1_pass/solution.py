import json

# Define the itinerary based on the reasoning above
itinerary = [
    {"day_range": "Day 1-5", "place": "Berlin"},
    {"day_range": "Day 5-7", "place": "Split"},
    {"day_range": "Day 7-11", "place": "Lyon"},
    {"day_range": "Day 11-15", "place": "Bucharest"},
    {"day_range": "Day 15-19", "place": "Riga"},
    {"day_range": "Day 19-22", "place": "Tallinn"}
]

# Convert the itinerary to JSON format
result = {"itinerary": itinerary}

# Output the result as JSON
print(json.dumps(result, indent=4))
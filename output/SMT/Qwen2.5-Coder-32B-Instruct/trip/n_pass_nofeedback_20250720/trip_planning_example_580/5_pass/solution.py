# Define the itinerary manually
itinerary = [
    {"day": 1, "place": "Geneva"},
    {"day": 2, "place": "Geneva"},
    {"day": 3, "place": "Geneva"},
    {"day": 4, "place": "Geneva"},
    {"day": 5, "place": "Geneva"},
    {"day": 6, "place": "Geneva"},
    {"day": 7, "place": "Geneva"},
    {"day": 8, "place": "Paris"},
    {"day": 9, "place": "Paris"},
    {"day": 10, "place": "Paris"},
    {"day": 11, "place": "Paris"},
    {"day": 12, "place": "Paris"},
    {"day": 13, "place": "Paris"},
    {"day": 14, "place": "Porto"},
    {"day": 15, "place": "Porto"},
    {"day": 16, "place": "Porto"},
    {"day": 17, "place": "Porto"},
    {"day": 18, "place": "Porto"},
    {"day": 19, "place": "Oslo"},
    {"day": 20, "place": "Oslo"},
    {"day": 21, "place": "Reykjavik"},
    {"day": 22, "place": "Reykjavik"},
    {"day": 23, "place": "Oslo"}
]

# Convert itinerary to JSON format
import json
print(json.dumps({"itinerary": itinerary}, indent=2))
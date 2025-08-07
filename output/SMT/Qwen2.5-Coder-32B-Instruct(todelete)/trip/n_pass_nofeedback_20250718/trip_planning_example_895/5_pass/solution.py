import json

# Manually constructed itinerary
itinerary = {
    "Day 1": "Brussels",
    "Day 2": "Brussels",
    "Day 3": "Reykjavik",
    "Day 4": "Reykjavik",
    "Day 5": "Reykjavik",
    "Day 6": "Venice",
    "Day 7": "Venice",
    "Day 8": "Lisbon",
    "Day 9": "Lisbon",
    "Day 10": "Lisbon",
    "Day 11": "Lisbon",
    "Day 12": "Santorini",
    "Day 13": "Santorini",
    "Day 14": "Santorini",
    "Day 15": "London",
    "Day 16": "London",
    "Day 17": "London"
}

# Print the itinerary in JSON format
print(json.dumps({"itinerary": itinerary}, indent=4))
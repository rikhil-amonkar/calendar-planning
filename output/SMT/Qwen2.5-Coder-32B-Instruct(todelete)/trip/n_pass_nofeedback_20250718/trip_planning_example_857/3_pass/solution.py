import json

# Define the manual itinerary
itinerary = {
    "Day 1": "Frankfurt",
    "Day 2": "Frankfurt",
    "Day 3": "Hamburg",
    "Day 4": "Hamburg",
    "Day 5": "Hamburg",
    "Day 6": "Hamburg",
    "Day 7": "Hamburg",
    "Day 8": "Hamburg",
    "Day 9": "Hamburg",
    "Day 10": "Mykonos",
    "Day 11": "Mykonos",
    "Day 12": "Mykonos",
    "Day 13": "Naples",
    "Day 14": "Naples",
    "Day 15": "Naples",
    "Day 16": "Manchester",
    "Day 17": "Manchester",
    "Day 18": "Manchester"
}

# Convert to JSON format
itinerary_json = json.dumps({"itinerary": itinerary}, indent=4)
print(itinerary_json)
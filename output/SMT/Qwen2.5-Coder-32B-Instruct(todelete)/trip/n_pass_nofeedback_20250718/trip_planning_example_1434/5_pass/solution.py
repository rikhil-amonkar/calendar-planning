import json

# Define the itinerary manually
itinerary = [
    {"day": 1, "place": "Frankfurt"},
    {"day": 2, "place": "Frankfurt"},
    {"day": 3, "place": "Frankfurt"},
    {"day": 4, "place": "Frankfurt"},
    {"day": 5, "place": "Frankfurt"},
    {"day": 6, "place": "Rome"},
    {"day": 7, "place": "Rome"},
    {"day": 8, "place": "Rome"},
    {"day": 9, "place": "Rome"},
    {"day": 10, "place": "Mykonos"},
    {"day": 11, "place": "Mykonos"},
    {"day": 12, "place": "Nice"},
    {"day": 13, "place": "Nice"},
    {"day": 14, "place": "Nice"},
    {"day": 15, "place": "Seville"},
    {"day": 16, "place": "Seville"},
    {"day": 17, "place": "Seville"},
    {"day": 18, "place": "Seville"},
    {"day": 19, "place": "Seville"},
    {"day": 20, "place": "Lisbon"},
    {"day": 21, "place": "Lisbon"},
    {"day": 22, "place": "Stuttgart"},
    {"day": 23, "place": "Stuttgart"}
]

# Create the JSON dictionary
itinerary_dict = {"itinerary": itinerary}
print(json.dumps(itinerary_dict, indent=2))
# Manually construct the itinerary based on the constraints and flight connections
itinerary = [
    {"day": 4, "place": "Paris"},
    {"day": 5, "place": "Paris"},
    {"day": 6, "place": "Paris"},
    {"day": 7, "place": "Paris"},
    {"day": 8, "place": "Paris"},
    {"day": 9, "place": "Warsaw"},
    {"day": 10, "place": "Warsaw"},
    {"day": 11, "place": "Tallinn"},
    {"day": 12, "place": "Tallinn"},
    {"day": 13, "place": "Riga"},
    {"day": 14, "place": "Riga"},
    {"day": 15, "place": "Krakow"},
    {"day": 16, "place": "Krakow"},
    {"day": 17, "place": "Krakow"},
    {"day": 18, "place": "Krakow"},
    {"day": 19, "place": "Helsinki"},
    {"day": 20, "place": "Helsinki"},
    {"day": 21, "place": "Helsinki"},
    {"day": 22, "place": "Helsinki"},
    {"day": 23, "place": "Helsinki"},
    {"day": 24, "place": "Santorini"},
    {"day": 25, "place": "Santorini"}
]

# Ensure the itinerary is sorted by day
itinerary.sort(key=lambda x: x["day"])

# Create the final dictionary
itinerary_dict = {"itinerary": itinerary}
print(itinerary_dict)
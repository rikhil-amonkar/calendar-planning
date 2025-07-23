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
    {"day": 12, "place": "Santorini"},
    {"day": 13, "place": "Santorini"},
    {"day": 14, "place": "Lyon"},
    {"day": 15, "place": "Lyon"},
    {"day": 16, "place": "Lyon"},
    {"day": 17, "place": "Lyon"},
    {"day": 18, "place": "Krakow"},
    {"day": 19, "place": "Helsinki"},
    {"day": 20, "place": "Helsinki"},
    {"day": 21, "place": "Helsinki"},
    {"day": 22, "place": "Helsinki"},
    {"day": 23, "place": "Helsinki"},
    {"day": 24, "place": "Riga"},
    {"day": 25, "place": "Riga"}
]

# Ensure the itinerary is sorted by day
itinerary.sort(key=lambda x: x["day"])

# Create the final dictionary
itinerary_dict = {"itinerary": itinerary}
print(itinerary_dict)
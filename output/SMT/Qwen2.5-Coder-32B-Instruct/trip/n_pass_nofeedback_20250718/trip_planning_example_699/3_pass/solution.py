# Manually constructed itinerary
itinerary = [
    {"day": 1, "place": "Hamburg"},
    {"day": 2, "place": "Hamburg"},
    {"day": 2, "place": "Dublin"},
    {"day": 3, "place": "Dublin"},
    {"day": 4, "place": "Dublin"},
    {"day": 5, "place": "Dublin"},
    {"day": 6, "place": "Dublin"},
    {"day": 7, "place": "London"},
    {"day": 8, "place": "London"},
    {"day": 9, "place": "London"},
    {"day": 9, "place": "Reykjavik"},
    {"day": 10, "place": "Reykjavik"},
    {"day": 11, "place": "London"},
    {"day": 12, "place": "Helsinki"},
    {"day": 13, "place": "Helsinki"},
    {"day": 14, "place": "Helsinki"},
    {"day": 15, "place": "Helsinki"},
    {"day": 13, "place": "Mykonos"},
    {"day": 14, "place": "Mykonos"},
    {"day": 15, "place": "Mykonos"}
]

# Remove duplicate entries and sort by day
itinerary_dict = {"itinerary": sorted(list({(entry["day"], entry["place"]) for entry in itinerary}), key=lambda x: x[0])}
itinerary_dict = {"itinerary": [{"day": day, "place": place} for day, place in itinerary_dict["itinerary"]]}
print(itinerary_dict)
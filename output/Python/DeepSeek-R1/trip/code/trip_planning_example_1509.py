import json

itinerary = [
    {"day_range": "Day 1-4", "place": "Lyon"},
    {"day_range": "Day 4-8", "place": "Paris"},
    {"day_range": "Day 8-12", "place": "Copenhagen"},
    {"day_range": "Day 12-13", "place": "Santorini"},
    {"day_range": "Day 13-17", "place": "Oslo"},
    {"day_range": "Day 17-18", "place": "Krakow"},
    {"day_range": "Day 18-22", "place": "Helsinki"},
    {"day_range": "Day 22-23", "place": "Warsaw"},
    {"day_range": "Day 23-24", "place": "Riga"},
    {"day_range": "Day 24-25", "place": "Tallinn"}
]

flight_routes = {
    "Lyon": ["Paris", "Oslo"],
    "Paris": ["Lyon", "Oslo", "Riga", "Tallinn", "Warsaw", "Helsinki", "Copenhagen", "Krakow"],
    "Copenhagen": ["Helsinki", "Warsaw", "Santorini", "Krakow", "Riga", "Oslo", "Tallinn"],
    "Santorini": ["Oslo"],
    "Oslo": ["Lyon", "Paris", "Riga", "Krakow", "Warsaw", "Helsinki", "Tallinn", "Santorini"],
    "Krakow": ["Helsinki", "Warsaw", "Paris", "Copenhagen", "Oslo"],
    "Helsinki": ["Copenhagen", "Warsaw", "Riga", "Tallinn", "Paris", "Oslo", "Krakow"],
    "Warsaw": ["Riga", "Tallinn", "Copenhagen", "Paris", "Helsinki", "Oslo", "Krakow"],
    "Riga": ["Warsaw", "Tallinn", "Copenhagen", "Helsinki", "Paris", "Oslo"],
    "Tallinn": ["Warsaw", "Copenhagen", "Oslo", "Helsinki", "Riga", "Paris"]
}

valid = True
prev_place = None
for entry in itinerary:
    current_place = entry["place"]
    if prev_place and current_place not in flight_routes.get(prev_place, []):
        valid = False
        break
    prev_place = current_place

if valid and len(itinerary) == 10:
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))
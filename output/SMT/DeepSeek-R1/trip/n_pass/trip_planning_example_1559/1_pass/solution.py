import json

itinerary = [
    {"day_range": "Day 1-2", "place": "Tallinn"},
    {"day_range": "Day 2", "place": "Tallinn"},
    {"day_range": "Day 2", "place": "Prague"},
    {"day_range": "Day 2-4", "place": "Prague"},
    {"day_range": "Day 4", "place": "Prague"},
    {"day_range": "Day 4", "place": "Valencia"},
    {"day_range": "Day 4-5", "place": "Valencia"},
    {"day_range": "Day 5", "place": "Valencia"},
    {"day_range": "Day 5", "place": "Seville"},
    {"day_range": "Day 5-9", "place": "Seville"},
    {"day_range": "Day 9", "place": "Seville"},
    {"day_range": "Day 9", "place": "Paris"},
    {"day_range": "Day 9-12", "place": "Paris"},
    {"day_range": "Day 12", "place": "Paris"},
    {"day_range": "Day 12", "place": "Lyon"},
    {"day_range": "Day 12-15", "place": "Lyon"},
    {"day_range": "Day 15", "place": "Lyon"},
    {"day_range": "Day 15", "place": "Oslo"},
    {"day_range": "Day 15-17", "place": "Oslo"},
    {"day_range": "Day 17", "place": "Oslo"},
    {"day_range": "Day 17", "place": "Lisbon"},
    {"day_range": "Day 17-18", "place": "Lisbon"},
    {"day_range": "Day 18", "place": "Lisbon"},
    {"day_range": "Day 18", "place": "Nice"},
    {"day_range": "Day 18-21", "place": "Nice"},
    {"day_range": "Day 21", "place": "Nice"},
    {"day_range": "Day 21", "place": "Mykonos"},
    {"day_range": "Day 21-25", "place": "Mykonos"}
]

result = {"itinerary": itinerary}
print(json.dumps(result))
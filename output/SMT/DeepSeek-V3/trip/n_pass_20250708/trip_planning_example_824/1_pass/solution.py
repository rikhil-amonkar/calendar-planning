import json

itinerary = {
    "itinerary": [
        {"day_range": "Day 1-5", "place": "Berlin"},
        {"day_range": "Day 5", "place": "Berlin"},
        {"day_range": "Day 5", "place": "Split"},
        {"day_range": "Day 5-7", "place": "Split"},
        {"day_range": "Day 7", "place": "Split"},
        {"day_range": "Day 7", "place": "Lyon"},
        {"day_range": "Day 7-11", "place": "Lyon"},
        {"day_range": "Day 11", "place": "Lyon"},
        {"day_range": "Day 11", "place": "Lisbon"},
        {"day_range": "Day 11-13", "place": "Lisbon"},
        {"day_range": "Day 13", "place": "Lisbon"},
        {"day_range": "Day 13", "place": "Bucharest"},
        {"day_range": "Day 13-15", "place": "Bucharest"},
        {"day_range": "Day 15", "place": "Bucharest"},
        {"day_range": "Day 15", "place": "Riga"},
        {"day_range": "Day 15-19", "place": "Riga"},
        {"day_range": "Day 19", "place": "Riga"},
        {"day_range": "Day 19", "place": "Tallinn"},
        {"day_range": "Day 19-22", "place": "Tallinn"}
    ]
}

print(json.dumps(itinerary, indent=2))
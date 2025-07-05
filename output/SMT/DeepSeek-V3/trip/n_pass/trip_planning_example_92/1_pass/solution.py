def solve_itinerary():
    itinerary = [
        {"day_range": "Day 1", "place": "Dublin"},
        {"day_range": "Day 2", "place": "Dublin"},
        {"day_range": "Day 2", "place": "Riga"},
        {"day_range": "Day 2-5", "place": "Riga"},
        {"day_range": "Day 6", "place": "Riga"},
        {"day_range": "Day 6", "place": "Vilnius"},
        {"day_range": "Day 6-12", "place": "Vilnius"}
    ]
    return {"itinerary": itinerary}

print(solve_itinerary())
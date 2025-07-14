def solve_itinerary():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Riga"},
        {"day_range": "Day 3", "place": "Amsterdam"},
        {"day_range": "Day 4", "place": "Amsterdam"},
        {"day_range": "Day 4", "place": "Mykonos"},
        {"day_range": "Day 5-7", "place": "Mykonos"}
    ]
    
    return {"itinerary": itinerary}

print(solve_itinerary())
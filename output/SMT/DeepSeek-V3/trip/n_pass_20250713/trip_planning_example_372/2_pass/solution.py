def generate_itinerary():
    itinerary = [
        {"day_range": "Day 1-4", "place": "Madrid"},
        {"day_range": "Day 4", "place": "Madrid"},
        {"day_range": "Day 4", "place": "Seville"},
        {"day_range": "Day 4-5", "place": "Seville"},
        {"day_range": "Day 5", "place": "Seville"},
        {"day_range": "Day 5", "place": "Porto"},
        {"day_range": "Day 5-7", "place": "Porto"},
        {"day_range": "Day 7", "place": "Porto"},
        {"day_range": "Day 7", "place": "Stuttgart"},
        {"day_range": "Day 7-10", "place": "Stuttgart"},
        {"day_range": "Day 10", "place": "Stuttgart"},
        {"day_range": "Day 10", "place": "Porto"},
        {"day_range": "Day 10-12", "place": "Porto"},
        {"day_range": "Day 12", "place": "Porto"},
        {"day_range": "Day 12", "place": "Stuttgart"},
        {"day_range": "Day 12-13", "place": "Stuttgart"}
    ]
    
    return {"itinerary": itinerary}

print(generate_itinerary())
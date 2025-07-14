def generate_itinerary():
    itinerary = [
        {"day_range": "Day 1-4", "place": "Madrid"},
        {"day_range": "Day 4", "place": "Madrid"},
        {"day_range": "Day 4", "place": "Seville"},
        {"day_range": "Day 4-5", "place": "Seville"},
        {"day_range": "Day 5", "place": "Seville"},
        {"day_range": "Day 5", "place": "Porto"},
        {"day_range": "Day 5-6", "place": "Porto"},
        {"day_range": "Day 6", "place": "Porto"},
        {"day_range": "Day 6", "place": "Stuttgart"},
        {"day_range": "Day 6-13", "place": "Stuttgart"}
    ]
    
    return {"itinerary": itinerary}

print(generate_itinerary())
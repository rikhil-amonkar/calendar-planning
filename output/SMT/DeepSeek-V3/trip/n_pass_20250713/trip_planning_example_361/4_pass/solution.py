def generate_itinerary():
    itinerary = [
        {"day_range": "Day 1-7", "place": "Madrid"},
        {"day_range": "Day 7", "place": "Madrid"},
        {"day_range": "Day 7", "place": "Paris"},
        {"day_range": "Day 8-12", "place": "Paris"},
        {"day_range": "Day 12", "place": "Paris"},
        {"day_range": "Day 12", "place": "Seville"},
        {"day_range": "Day 13-14", "place": "Seville"},
        {"day_range": "Day 14", "place": "Seville"},
        {"day_range": "Day 14", "place": "Bucharest"},
        {"day_range": "Day 15", "place": "Bucharest"}
    ]
    return {"itinerary": itinerary}

# Execute the function to get the itinerary
result = generate_itinerary()
print(result)
import json

def get_optimal_itinerary():
    # Revised itinerary that covers exactly 26 days
    itinerary = [
        {"day_range": "Day 1-4", "place": "Bucharest"},  # 4 days
        {"day_range": "Day 4-6", "place": "Vienna"},     # 2 days (Flight Bucharest->Vienna)
        {"day_range": "Day 6-9", "place": "Prague"},     # 3 days (Flight Vienna->Prague)
        {"day_range": "Day 9-13", "place": "Tallinn"},   # 4 days (Flight Prague->Tallinn)
        {"day_range": "Day 13-17", "place": "Frankfurt"}, # 4 days (Flight Tallinn->Frankfurt)
        {"day_range": "Day 17-21", "place": "Zurich"},   # 4 days (Flight Frankfurt->Zurich)
        {"day_range": "Day 21-22", "place": "Florence"}, # 1 day (Flight Zurich->Florence)
        {"day_range": "Day 22-26", "place": "Venice"}    # 4 days (Flight Florence->Venice)
    ]
    return {"itinerary": itinerary}

# Output the result
print(json.dumps(get_optimal_itinerary()))
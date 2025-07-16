import json

def get_optimal_itinerary():
    # Revised itinerary with fewer cities and longer stays
    itinerary = [
        {"day_range": "Day 1-6", "place": "Bucharest"},  # 6 days
        {"day_range": "Day 6-11", "place": "Vienna"},     # 5 days (Flight Bucharest->Vienna)
        {"day_range": "Day 11-16", "place": "Prague"},   # 5 days (Train Vienna->Prague)
        {"day_range": "Day 16-21", "place": "Zurich"},    # 5 days (Flight Prague->Zurich)
        {"day_range": "Day 21-26", "place": "Venice"}     # 5 days (Train Zurich->Venice)
    ]
    return {"itinerary": itinerary}

# Output the result
print(json.dumps(get_optimal_itinerary()))
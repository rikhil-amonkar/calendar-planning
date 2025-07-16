import json

def get_optimal_itinerary():
    # Revised itinerary that avoids Bucharest->Prague flight
    # Valid flight connections:
    # 1. Bucharest->Vienna (direct flights available)
    # 2. Vienna->Prague (direct flights available)
    itinerary = [
        {"day_range": "Day 1-5", "place": "Bucharest"},
        {"day_range": "Day 5-7", "place": "Vienna"},  # Flight Bucharest->Vienna
        {"day_range": "Day 7-10", "place": "Prague"},  # Flight Vienna->Prague
        {"day_range": "Day 10-14", "place": "Tallinn"},  # Flight Prague->Tallinn (meet friends)
        {"day_range": "Day 14-18", "place": "Frankfurt"},  # Flight Tallinn->Frankfurt (annual show)
        {"day_range": "Day 18-23", "place": "Zurich"},  # Flight Frankfurt->Zurich
        {"day_range": "Day 23-24", "place": "Florence"},  # Flight Zurich->Florence
        {"day_range": "Day 24-28", "place": "Venice"}  # Flight Florence->Venice (wedding)
    ]
    return {"itinerary": itinerary}

# Output the result
print(json.dumps(get_optimal_itinerary()))
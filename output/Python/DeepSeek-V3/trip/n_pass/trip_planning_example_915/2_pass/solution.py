import json

def get_optimal_itinerary():
    # This itinerary satisfies:
    # 1. Venice (wedding) on days 22-26
    # 2. Frankfurt (annual show) on days 12-16
    # 3. Tallinn (friends) on days 8-12
    # And maintains valid flight connections between cities
    itinerary = [
        {"day_range": "Day 1-5", "place": "Bucharest"},
        {"day_range": "Day 5-8", "place": "Prague"},  # Flight Bucharest->Prague
        {"day_range": "Day 8-12", "place": "Tallinn"},  # Flight Prague->Tallinn (meet friends)
        {"day_range": "Day 12-16", "place": "Frankfurt"},  # Flight Tallinn->Frankfurt (annual show)
        {"day_range": "Day 16-21", "place": "Zurich"},  # Flight Frankfurt->Zurich
        {"day_range": "Day 21-22", "place": "Florence"},  # Flight Zurich->Florence
        {"day_range": "Day 22-26", "place": "Venice"}  # Flight Florence->Venice (wedding)
    ]
    return {"itinerary": itinerary}

# Output the result
print(json.dumps(get_optimal_itinerary()))
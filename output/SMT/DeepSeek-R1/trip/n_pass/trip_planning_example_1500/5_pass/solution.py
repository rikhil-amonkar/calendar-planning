import json

itinerary = [
    {"day_range": "Day 1-3", "place": "London"},
    {"day_range": "Day 3", "place": "London"},
    {"day_range": "Day 3", "place": "Milan"},
    {"day_range": "Day 3-7", "place": "Milan"},
    {"day_range": "Day 7", "place": "Milan"},
    {"day_range": "Day 7", "place": "Zurich"},
    {"day_range": "Day 7-8", "place": "Zurich"},
    {"day_range": "Day 8", "place": "Zurich"},
    {"day_range": "Day 8", "place": "Hamburg"},
    {"day_range": "Day 8-9", "place": "Hamburg"},
    {"day_range": "Day 9", "place": "Hamburg"},
    {"day_range": "Day 9", "place": "Reykjavik"},
    {"day_range": "Day 9-13", "place": "Reykjavik"},
    {"day_range": "Day 13", "place": "Reykjavik"},
    {"day_range": "Day 13", "place": "Hamburg"},
    {"day_range": "Day 13-17", "place": "Hamburg"},
    {"day_range": "Day 17", "place": "Hamburg"},
    {"day_range": "Day 17", "place": "Stuttgart"},
    {"day_range": "Day 17-21", "place": "Stuttgart"},
    {"day_range": "Day 21", "place": "Stuttgart"},
    {"day_range": "Day 21", "place": "Barcelona"},
    {"day_range": "Day 21-25", "place": "Barcelona"},
    {"day_range": "Day 25", "place": "Barcelona"},
    {"day_range": "Day 25", "place": "Bucharest"},
    {"day_range": "Day 25-27", "place": "Bucharest"},
    {"day_range": "Day 27", "place": "Bucharest"},
    {"day_range": "Day 27", "place": "Tallinn"},
    {"day_range": "Day 27-28", "place": "Tallinn"}
]

result = {"itinerary": itinerary}
print(json.dumps(result))
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
    {"day_range": "Day 8", "place": "Stuttgart"},
    {"day_range": "Day 8-9", "place": "Stuttgart"},
    {"day_range": "Day 9", "place": "Stuttgart"},
    {"day_range": "Day 9", "place": "Reykjavik"},
    {"day_range": "Day 9-13", "place": "Reykjavik"},
    {"day_range": "Day 13", "place": "Reykjavik"},
    {"day_range": "Day 13", "place": "Hamburg"},
    {"day_range": "Day 13-17", "place": "Hamburg"},
    {"day_range": "Day 17", "place": "Hamburg"},
    {"day_range": "Day 17", "place": "Barcelona"},
    {"day_range": "Day 17-21", "place": "Barcelona"},
    {"day_range": "Day 21", "place": "Barcelona"},
    {"day_range": "Day 21", "place": "Bucharest"},
    {"day_range": "Day 21-22", "place": "Bucharest"},
    {"day_range": "Day 22", "place": "Bucharest"},
    {"day_range": "Day 22", "place": "Tallinn"},
    {"day_range": "Day 22-26", "place": "Tallinn"},
    {"day_range": "Day 26", "place": "Tallinn"},
    {"day_range": "Day 26", "place": "Stockholm"},
    {"day_range": "Day 26-28", "place": "Stockholm"}
]

result = {"itinerary": itinerary}
print(json.dumps(result))
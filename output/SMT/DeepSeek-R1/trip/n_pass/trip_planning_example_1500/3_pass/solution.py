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
    {"day_range": "Day 13", "place": "Stuttgart"},
    {"day_range": "Day 13-14", "place": "Stuttgart"},
    {"day_range": "Day 14", "place": "Stuttgart"},
    {"day_range": "Day 14", "place": "Hamburg"},
    {"day_range": "Day 14-17", "place": "Hamburg"},
    {"day_range": "Day 17", "place": "Hamburg"},
    {"day_range": "Day 17", "place": "Barcelona"},
    {"day_range": "Day 17-20", "place": "Barcelona"},
    {"day_range": "Day 20", "place": "Barcelona"},
    {"day_range": "Day 20", "place": "Bucharest"},
    {"day_range": "Day 20-22", "place": "Bucharest"},
    {"day_range": "Day 22", "place": "Bucharest"},
    {"day_range": "Day 22", "place": "Tallinn"},
    {"day_range": "Day 22-25", "place": "Tallinn"},
    {"day_range": "Day 25", "place": "Tallinn"},
    {"day_range": "Day 25", "place": "Stockholm"},
    {"day_range": "Day 25-28", "place": "Stockholm"}
]

result = {"itinerary": itinerary}
print(json.dumps(result))
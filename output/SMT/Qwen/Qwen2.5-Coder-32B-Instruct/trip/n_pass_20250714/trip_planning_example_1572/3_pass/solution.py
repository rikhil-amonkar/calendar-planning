# Manual construction of the itinerary
itinerary = [
    {"day_range": "Day 1-2", "place": "Berlin"},
    {"day_range": "Day 3", "place": "Berlin"},
    {"day_range": "Day 3", "place": "Paris"},
    {"day_range": "Day 4", "place": "Paris"},
    {"day_range": "Day 5-9", "place": "Paris"},
    {"day_range": "Day 10", "place": "Paris"},
    {"day_range": "Day 10", "place": "Nice"},
    {"day_range": "Day 11", "place": "Nice"},
    {"day_range": "Day 12-13", "place": "Nice"},
    {"day_range": "Day 14", "place": "Nice"},
    {"day_range": "Day 14", "place": "Zurich"},
    {"day_range": "Day 15-19", "place": "Zurich"},
    {"day_range": "Day 20", "place": "Zurich"},
    {"day_range": "Day 20", "place": "Stockholm"},
    {"day_range": "Day 21-22", "place": "Stockholm"},
    {"day_range": "Day 23", "place": "Stockholm"}
]

# Ensure the total duration is exactly 23 days
total_days = sum(len(day_range.split('-')) for entry in itinerary for day_range in entry["day_range"].split(','))
assert total_days == 23, "Total duration is not 23 days"

# Print the result in JSON format
print({"itinerary": itinerary})
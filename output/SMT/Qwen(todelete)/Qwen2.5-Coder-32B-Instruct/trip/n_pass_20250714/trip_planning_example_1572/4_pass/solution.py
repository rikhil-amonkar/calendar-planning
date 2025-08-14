# Manual construction of the itinerary
itinerary = [
    {"day_range": "Day 1-2", "place": "Berlin"},
    {"day_range": "Day 3", "place": "Berlin"},
    {"day_range": "Day 3", "place": "Paris"},
    {"day_range": "Day 4-8", "place": "Paris"},
    {"day_range": "Day 9", "place": "Paris"},
    {"day_range": "Day 9", "place": "Nice"},
    {"day_range": "Day 10-11", "place": "Nice"},
    {"day_range": "Day 12", "place": "Nice"},
    {"day_range": "Day 12", "place": "Zurich"},
    {"day_range": "Day 13-17", "place": "Zurich"},
    {"day_range": "Day 18", "place": "Zurich"},
    {"day_range": "Day 18", "place": "Stockholm"},
    {"day_range": "Day 19-21", "place": "Stockholm"},
    {"day_range": "Day 22", "place": "Stockholm"},
    {"day_range": "Day 22", "place": "Milan"},
    {"day_range": "Day 23", "place": "Milan"}
]

# Ensure the total duration is exactly 23 days
def count_days(itinerary):
    total_days = 0
    for entry in itinerary:
        day_range = entry["day_range"]
        if '-' in day_range:
            start, end = map(int, day_range.split('-'))
            total_days += end - start + 1
        else:
            total_days += 1
    return total_days

total_days = count_days(itinerary)
assert total_days == 23, "Total duration is not 23 days"

# Print the result in JSON format
print({"itinerary": itinerary})
# Define the itinerary manually
itinerary = [
    {"day_range": "Day 1-2", "place": "Reykjavik"},
    {"day_range": "Day 3", "place": "Reykjavik"},
    {"day_range": "Day 3", "place": "Stockholm"},
    {"day_range": "Day 3-4", "place": "Stockholm"},
    {"day_range": "Day 5", "place": "Stockholm"},
    {"day_range": "Day 5", "place": "Nice"},
    {"day_range": "Day 5-7", "place": "Nice"},
    {"day_range": "Day 8", "place": "Nice"},
    {"day_range": "Day 8-11", "place": "Venice"},
    {"day_range": "Day 12", "place": "Venice"},
    {"day_range": "Day 12-14", "place": "Vienna"},
    {"day_range": "Day 15", "place": "Vienna"},
    {"day_range": "Day 15-17", "place": "Split"}
]

# Adjust the itinerary to ensure it covers exactly 17 days
adjusted_itinerary = []

current_day = 1
for entry in itinerary:
    start_day, end_day = map(int, entry["day_range"].split('-')[-1].split('Day ')[-1].split('-'))
    if len(entry["day_range"].split('-')) == 2:
        adjusted_itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": entry["place"]})
        current_day = end_day + 1
    else:
        adjusted_itinerary.append({"day_range": f"Day {start_day}", "place": entry["place"]})
        current_day = start_day + 1

# Ensure the itinerary covers exactly 17 days
if current_day < 18:
    adjusted_itinerary.append({"day_range": f"Day {current_day}-17", "place": adjusted_itinerary[-1]["place"]})

# Print the adjusted itinerary
print({"itinerary": adjusted_itinerary})
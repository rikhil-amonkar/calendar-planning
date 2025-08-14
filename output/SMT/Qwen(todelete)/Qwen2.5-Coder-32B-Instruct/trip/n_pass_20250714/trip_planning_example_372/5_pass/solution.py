import json

# Define the itinerary manually
itinerary = [
    {"day_range": "Day 1-4", "place": "Madrid"},
    {"day_range": "Day 4", "place": "Madrid"},
    {"day_range": "Day 5", "place": "Porto"},
    {"day_range": "Day 5-7", "place": "Porto"},
    {"day_range": "Day 7", "place": "Porto"},
    {"day_range": "Day 8", "place": "Seville"},
    {"day_range": "Day 8-9", "place": "Seville"},
    {"day_range": "Day 9", "place": "Seville"},
    {"day_range": "Day 10", "place": "Stuttgart"},
    {"day_range": "Day 7-13", "place": "Stuttgart"},
    {"day_range": "Day 13", "place": "Stuttgart"}
]

# Remove duplicate entries for transition days
unique_itinerary = []
seen_days = set()

for entry in itinerary:
    day_range = entry["day_range"]
    place = entry["place"]
    start_day, end_day = map(int, day_range.split('-')[0].split()[1]), map(int, day_range.split('-')[1].split()[1])
    
    for day in range(start_day, end_day + 1):
        if (day, place) not in seen_days:
            unique_itinerary.append({"day_range": f"Day {day}", "place": place})
            seen_days.add((day, place))
        else:
            unique_itinerary.append({"day_range": f"Day {day}-{end_day}", "place": place})
            seen_days.add((day, place))

# Sort itinerary by day range
unique_itinerary.sort(key=lambda x: int(x["day_range"].split('-')[0].split()[1]))

# Print the itinerary in JSON format
print(json.dumps({"itinerary": unique_itinerary}, indent=2))
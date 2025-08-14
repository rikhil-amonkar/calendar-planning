# Manually constructed itinerary
itinerary = [
    {"day_range": "Day 1-7", "place": "Manchester"},
    {"day_range": "Day 8", "place": "Manchester"},
    {"day_range": "Day 8", "place": "Vienna"},
    {"day_range": "Day 8-9", "place": "Vienna"},
    {"day_range": "Day 10", "place": "Vienna"},
    {"day_range": "Day 10", "place": "Stuttgart"},
    {"day_range": "Day 10-14", "place": "Stuttgart"},
    {"day_range": "Day 15", "place": "Stuttgart"},
    {"day_range": "Day 15", "place": "Madrid"},
    {"day_range": "Day 15", "place": "Madrid"}
]

# Remove duplicate entries for the same day
unique_itinerary = []
seen_days = set()

for entry in itinerary:
    day_range = entry["day_range"]
    if "-" in day_range:
        start_day, end_day = int(day_range.split('-')[0].split()[1]), int(day_range.split('-')[1].split()[1])
        for day in range(start_day, end_day + 1):
            if day not in seen_days:
                unique_itinerary.append({"day_range": f"Day {day}", "place": entry["place"]})
                seen_days.add(day)
    else:
        day = int(day_range.split()[1])
        if day not in seen_days:
            unique_itinerary.append({"day_range": f"Day {day}", "place": entry["place"]})
            seen_days.add(day)

# Sort the itinerary by day range
unique_itinerary.sort(key=lambda x: int(x['day_range'].split()[1]))

# Print the itinerary in JSON format
print({"itinerary": unique_itinerary})
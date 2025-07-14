# Manually constructed itinerary
itinerary = [
    {"day_range": "Day 1-3", "place": "Zurich"},
    {"day_range": "Day 4-4", "place": "Zurich"},
    {"day_range": "Day 4-4", "place": "Helsinki"},
    {"day_range": "Day 5-5", "place": "Helsinki"},
    {"day_range": "Day 6-7", "place": "Helsinki"},
    {"day_range": "Day 8-8", "place": "Helsinki"},
    {"day_range": "Day 8-8", "place": "Bucharest"},
    {"day_range": "Day 9-9", "place": "Bucharest"},
    {"day_range": "Day 10-11", "place": "Bucharest"},
    {"day_range": "Day 12-12", "place": "Bucharest"},
    {"day_range": "Day 12-12", "place": "Split"},
    {"day_range": "Day 12-18", "place": "Split"}
]

# Adjust the itinerary to remove duplicates and ensure correct ranges
adjusted_itinerary = []
current_day = 1

for entry in itinerary:
    start_day, end_day = map(int, entry["day_range"].split(" ")[1].split("-"))
    if current_day != start_day:
        adjusted_itinerary.append({"day_range": f"Day {current_day}-{start_day-1}", "place": "Travel"})
    adjusted_itinerary.append(entry)
    current_day = end_day + 1

# Ensure the last day is covered
if current_day <= total_days:
    adjusted_itinerary.append({"day_range": f"Day {current_day}-{total_days}", "place": "Travel"})

# Remove duplicate entries for travel days
final_itinerary = []
last_entry = None
for entry in adjusted_itinerary:
    if entry != last_entry:
        final_itinerary.append(entry)
    last_entry = entry

print({"itinerary": final_itinerary})
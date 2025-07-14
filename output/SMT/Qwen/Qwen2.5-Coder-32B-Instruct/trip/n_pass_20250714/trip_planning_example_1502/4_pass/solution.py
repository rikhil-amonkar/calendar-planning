# Define the itinerary manually
itinerary = [
    {"day_range": "Day 1-3", "place": "Santorini"},
    {"day_range": "Day 4-5", "place": "Madrid"},
    {"day_range": "Day 6-7", "place": "Madrid"},
    {"day_range": "Day 8-11", "place": "Valencia"},
    {"day_range": "Day 12-13", "place": "Seville"},
    {"day_range": "Day 14-16", "place": "Bucharest"},
    {"day_range": "Day 17-20", "place": "Vienna"},
    {"day_range": "Day 21-24", "place": "Riga"},
    {"day_range": "Day 25-27", "place": "Tallinn"},
    {"day_range": "Day 18-22", "place": "Krakow"},
    {"day_range": "Day 23-26", "place": "Frankfurt"}
]

# Add flight days
flight_days = [
    {"day_range": "Day 5", "place": "Madrid"},
    {"day_range": "Day 5", "place": "Valencia"},
    {"day_range": "Day 11", "place": "Valencia"},
    {"day_range": "Day 11", "place": "Seville"},
    {"day_range": "Day 13", "place": "Seville"},
    {"day_range": "Day 13", "place": "Bucharest"},
    {"day_range": "Day 16", "place": "Bucharest"},
    {"day_range": "Day 16", "place": "Vienna"},
    {"day_range": "Day 20", "place": "Vienna"},
    {"day_range": "Day 20", "place": "Riga"},
    {"day_range": "Day 24", "place": "Riga"},
    {"day_range": "Day 24", "place": "Tallinn"},
    {"day_range": "Day 27", "place": "Tallinn"},
    {"day_range": "Day 22", "place": "Krakow"},
    {"day_range": "Day 22", "place": "Frankfurt"},
    {"day_range": "Day 26", "place": "Frankfurt"}
]

# Combine itinerary and flight days
full_itinerary = itinerary + flight_days

# Sort the full itinerary by day
full_itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split('-')[0]))

# Remove duplicates and ensure no gaps or overlaps
final_itinerary = []
current_day = 1
for entry in full_itinerary:
    start_day, end_day = map(int, entry["day_range"].split()[1].split('-'))
    if start_day > current_day:
        # Add a gap entry if there is a gap
        final_itinerary.append({"day_range": f"Day {current_day}-{start_day-1}", "place": "Travel"})
    final_itinerary.append(entry)
    current_day = end_day + 1

# Ensure the last day is covered
if current_day <= total_days:
    final_itinerary.append({"day_range": f"Day {current_day}-{total_days}", "place": "Travel"})

# Print the final itinerary
print({"itinerary": final_itinerary})
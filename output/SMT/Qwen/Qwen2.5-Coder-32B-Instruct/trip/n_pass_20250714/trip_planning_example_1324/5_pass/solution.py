itinerary = [
    {"day_range": "Day 1-4", "place": "Venice"},
    {"day_range": "Day 4-6", "place": "Barcelona"},
    {"day_range": "Day 7-9", "place": "Barcelona"},
    {"day_range": "Day 10-13", "place": "Copenhagen"},
    {"day_range": "Day 14-17", "place": "Copenhagen"},
    {"day_range": "Day 18-21", "place": "Lyon"},
    {"day_range": "Day 22-25", "place": "Reykjavik"},
    {"day_range": "Day 26", "place": "Dubrovnik"},
    {"day_range": "Day 21-22", "place": "Athens"},
    {"day_range": "Day 23-26", "place": "Tallinn"}
]

# Remove duplicate entries and ensure correct sequence
unique_itinerary = []
current_day = 1

for item in itinerary:
    start_day = int(item["day_range"].split()[1].split('-')[0])
    end_day = int(item["day_range"].split()[1].split('-')[-1]) if '-' in item["day_range"] else start_day
    if start_day >= current_day:
        unique_itinerary.append(item)
        current_day = end_day + 1

# Sort the itinerary by day range
unique_itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split('-')[0]))

print({"itinerary": unique_itinerary})
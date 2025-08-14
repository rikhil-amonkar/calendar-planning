itinerary = [
    {"day_range": "Day 1-4", "place": "Venice"},
    {"day_range": "Day 4", "place": "Barcelona"},
    {"day_range": "Day 4-6", "place": "Barcelona"},
    {"day_range": "Day 7-9", "place": "Barcelona"},
    {"day_range": "Day 10-13", "place": "Copenhagen"},
    {"day_range": "Day 10", "place": "Copenhagen"},
    {"day_range": "Day 13", "place": "Copenhagen"},
    {"day_range": "Day 14-17", "place": "Copenhagen"},
    {"day_range": "Day 14", "place": "Copenhagen"},
    {"day_range": "Day 17", "place": "Copenhagen"},
    {"day_range": "Day 18-21", "place": "Lyon"},
    {"day_range": "Day 18", "place": "Lyon"},
    {"day_range": "Day 21", "place": "Lyon"},
    {"day_range": "Day 22-25", "place": "Reykjavik"},
    {"day_range": "Day 22", "place": "Reykjavik"},
    {"day_range": "Day 25", "place": "Reykjavik"},
    {"day_range": "Day 26", "place": "Dubrovnik"},
    {"day_range": "Day 21-22", "place": "Athens"},
    {"day_range": "Day 21", "place": "Athens"},
    {"day_range": "Day 22", "place": "Athens"},
    {"day_range": "Day 23-26", "place": "Tallinn"},
    {"day_range": "Day 23", "place": "Tallinn"},
    {"day_range": "Day 24", "place": "Tallinn"},
    {"day_range": "Day 25", "place": "Tallinn"},
    {"day_range": "Day 26", "place": "Tallinn"}
]

# Remove duplicate entries
unique_itinerary = []
for item in itinerary:
    if item not in unique_itinerary:
        unique_itinerary.append(item)

# Sort the itinerary by day range
unique_itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split('-')[0]))

print({"itinerary": unique_itinerary})
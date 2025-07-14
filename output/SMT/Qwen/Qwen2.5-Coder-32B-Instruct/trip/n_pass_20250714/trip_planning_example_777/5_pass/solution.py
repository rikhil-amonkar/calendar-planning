# Define the itinerary manually
itinerary = [
    {"day_range": "Day 1-5", "place": "Dublin"},
    {"day_range": "Day 5", "place": "Dublin"},
    {"day_range": "Day 6-8", "place": "Helsinki"},
    {"day_range": "Day 8", "place": "Helsinki"},
    {"day_range": "Day 9-11", "place": "Riga"},
    {"day_range": "Day 11", "place": "Riga"},
    {"day_range": "Day 7-11", "place": "Tallinn"},
    {"day_range": "Day 11", "place": "Tallinn"},
    {"day_range": "Day 12-13", "place": "Reykjavik"},
    {"day_range": "Day 13", "place": "Reykjavik"},
    {"day_range": "Day 14-15", "place": "Vienna"},
    {"day_range": "Day 15", "place": "Vienna"}
]

# Ensure the itinerary covers exactly 15 days
last_day = max(int(item["day_range"].split()[1].split('-')[-1]) for item in itinerary)
if last_day == 15:
    print({"itinerary": itinerary})
else:
    print("Itinerary does not cover exactly 15 days")
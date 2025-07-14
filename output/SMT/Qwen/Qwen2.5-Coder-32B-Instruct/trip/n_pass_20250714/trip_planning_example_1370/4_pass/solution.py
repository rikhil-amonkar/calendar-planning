# Define the itinerary manually
itinerary = [
    {"day_range": "Day 1-5", "place": "Paris"},
    {"day_range": "Day 6", "place": "Paris"},
    {"day_range": "Day 6", "place": "Krakow"},
    {"day_range": "Day 7-11", "place": "Krakow"},
    {"day_range": "Day 12", "place": "Krakow"},
    {"day_range": "Day 12", "place": "Vilnius"},
    {"day_range": "Day 13-15", "place": "Vilnius"},
    {"day_range": "Day 16", "place": "Vilnius"},
    {"day_range": "Day 16", "place": "Munich"},
    {"day_range": "Day 17-21", "place": "Munich"},
    {"day_range": "Day 22", "place": "Munich"},
    {"day_range": "Day 22", "place": "Geneva"},
    {"day_range": "Day 23-24", "place": "Geneva"},
    {"day_range": "Day 25", "place": "Geneva"},
    {"day_range": "Day 25", "place": "Amsterdam"},
    {"day_range": "Day 26-29", "place": "Amsterdam"},
    {"day_range": "Day 30", "place": "Amsterdam"},
    {"day_range": "Day 30", "place": "Budapest"},
    {"day_range": "Day 30", "place": "Budapest"}
]

# Remove duplicate entries for the same day
unique_itinerary = []
for entry in itinerary:
    if not unique_itinerary or unique_itinerary[-1] != entry:
        unique_itinerary.append(entry)

# Print the result
print({"itinerary": unique_itinerary})
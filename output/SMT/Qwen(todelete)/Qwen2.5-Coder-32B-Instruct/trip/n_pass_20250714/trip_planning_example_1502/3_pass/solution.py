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

# Print the final itinerary
print({"itinerary": full_itinerary})
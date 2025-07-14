# Manually constructing the itinerary
itinerary = [
    {"day_range": "Day 1-4", "place": "Vilnius"},
    {"day_range": "Day 4", "place": "Vilnius"},
    {"day_range": "Day 4", "place": "Munich"},
    {"day_range": "Day 5-7", "place": "Munich"},
    {"day_range": "Day 7", "place": "Munich"},
    {"day_range": "Day 7", "place": "Mykonos"},
    {"day_range": "Day 8-12", "place": "Mykonos"}
]

# Print the result as a JSON-formatted dictionary
print({"itinerary": itinerary})
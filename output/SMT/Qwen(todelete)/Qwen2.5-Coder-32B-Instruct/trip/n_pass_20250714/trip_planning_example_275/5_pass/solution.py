# Manually construct the itinerary
itinerary = [
    {"day_range": "Day 1-5", "place": "Split"},
    {"day_range": "Day 5", "place": "Split"},
    {"day_range": "Day 5", "place": "Vilnius"},
    {"day_range": "Day 5-8", "place": "Vilnius"},
    {"day_range": "Day 8", "place": "Vilnius"},
    {"day_range": "Day 8", "place": "Madrid"},
    {"day_range": "Day 8-13", "place": "Madrid"},
    {"day_range": "Day 13", "place": "Madrid"},
    {"day_range": "Day 13", "place": "Santorini"},
    {"day_range": "Day 13-14", "place": "Santorini"}
]

# Print the itinerary in JSON format
print({"itinerary": itinerary})
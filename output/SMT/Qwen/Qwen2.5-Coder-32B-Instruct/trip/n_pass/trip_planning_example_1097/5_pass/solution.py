# Final itinerary in JSON format
itinerary = [
    {"day_range": "Day 1-4", "place": "Reykjavik"},
    {"day_range": "Day 4", "place": "Reykjavik"},
    {"day_range": "Day 4-5", "place": "Riga"},
    {"day_range": "Day 5", "place": "Riga"},
    {"day_range": "Day 5-7", "place": "Oslo"},
    {"day_range": "Day 6", "place": "Oslo"},
    {"day_range": "Day 7", "place": "Oslo"},
    {"day_range": "Day 7-8", "place": "Dubrovnik"},
    {"day_range": "Day 8", "place": "Dubrovnik"},
    {"day_range": "Day 8-9", "place": "Madrid"},
    {"day_range": "Day 9", "place": "Madrid"},
    {"day_range": "Day 9-12", "place": "Warsaw"},
    {"day_range": "Day 10", "place": "Warsaw"},
    {"day_range": "Day 11", "place": "Warsaw"},
    {"day_range": "Day 12", "place": "Warsaw"},
    {"day_range": "Day 12-14", "place": "London"},
    {"day_range": "Day 13", "place": "London"},
    {"day_range": "Day 14", "place": "London"},
    {"day_range": "Day 14-18", "place": "Lyon"},
    {"day_range": "Day 15", "place": "Lyon"},
    {"day_range": "Day 16", "place": "Lyon"},
    {"day_range": "Day 17", "place": "Lyon"},
    {"day_range": "Day 18", "place": "Lyon"}
]

# Convert to JSON format
itinerary_json = json.dumps({"itinerary": itinerary}, indent=4)
print(itinerary_json)
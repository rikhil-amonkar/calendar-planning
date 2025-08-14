# Manually constructed itinerary
itinerary = [
    {"day": i, "place": "Split"} for i in range(1, 7)
] + [
    {"day": i, "place": "London"} for i in range(7, 14)
] + [
    {"day": i, "place": "Santorini"} for i in range(14, 19)
]

# Print the itinerary in JSON format
print({"itinerary": itinerary})
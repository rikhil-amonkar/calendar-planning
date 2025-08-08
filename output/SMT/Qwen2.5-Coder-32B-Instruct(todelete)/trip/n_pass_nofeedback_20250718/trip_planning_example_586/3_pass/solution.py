import json

# Define the itinerary manually
itinerary = [
    {"day": 1, "place": "Prague"},
    {"day": 2, "place": "Prague"},
    {"day": 3, "place": "Helsinki"},
    {"day": 4, "place": "Helsinki"},
    {"day": 5, "place": "Helsinki"},
    {"day": 6, "place": "Helsinki"},
    {"day": 7, "place": "Frankfurt"},
    {"day": 8, "place": "Frankfurt"},
    {"day": 9, "place": "Frankfurt"},
    {"day": 10, "place": "Lyon"},
    {"day": 11, "place": "Lyon"},
    {"day": 12, "place": "Lyon"},
    {"day": 12, "place": "Naples"}
]

# Remove duplicate entries for day 12
final_itinerary = []
for entry in itinerary:
    if entry not in final_itinerary:
        final_itinerary.append(entry)

# Ensure the final itinerary is in the correct format
final_itinerary = [{"day": entry["day"], "place": entry["place"]} for entry in final_itinerary]

# Print the final itinerary in JSON format
print(json.dumps({"itinerary": final_itinerary}, indent=2))
import json

# Define the itinerary based on the manually defined sequence
itinerary = [
    {"day": 1, "place": "Dubrovnik"},
    {"day": 2, "place": "Dubrovnik"},
    {"day": 3, "place": "Dubrovnik"},
    {"day": 4, "place": "Dubrovnik"},
    {"day": 5, "place": "Helsinki"},
    {"day": 6, "place": "Helsinki"},
    {"day": 7, "place": "Helsinki"},
    {"day": 8, "place": "Helsinki"},
    {"day": 9, "place": "Reykjavik"},
    {"day": 10, "place": "Reykjavik"},
    {"day": 11, "place": "Reykjavik"},
    {"day": 12, "place": "Reykjavik"},
    {"day": 13, "place": "Prague"},
    {"day": 14, "place": "Prague"},
    {"day": 15, "place": "Prague"},
    {"day": 16, "place": "Valencia"},
    {"day": 17, "place": "Valencia"},
    {"day": 18, "place": "Valencia"},
    {"day": 16, "place": "Porto"},
    {"day": 17, "place": "Porto"},
    {"day": 18, "place": "Porto"}
]

# Remove duplicate entries for the same day
unique_itinerary = []
seen_days = set()
for entry in itinerary:
    if entry["day"] not in seen_days:
        unique_itinerary.append(entry)
        seen_days.add(entry["day"])

# Ensure the itinerary is sorted by day
unique_itinerary.sort(key=lambda x: x["day"])

# Adjust the itinerary to ensure the friend meeting in Porto is between day 16 and day 18
final_itinerary = []
for entry in unique_itinerary:
    if entry["day"] == 16:
        final_itinerary.append({"day": 16, "place": "Valencia"})
        final_itinerary.append({"day": 16, "place": "Porto"})
    elif entry["day"] == 17:
        final_itinerary.append({"day": 17, "place": "Valencia"})
        final_itinerary.append({"day": 17, "place": "Porto"})
    elif entry["day"] == 18:
        final_itinerary.append({"day": 18, "place": "Valencia"})
        final_itinerary.append({"day": 18, "place": "Porto"})
    else:
        final_itinerary.append(entry)

# Remove duplicate entries for the same day
unique_final_itinerary = []
seen_days = set()
for entry in final_itinerary:
    if entry["day"] not in seen_days:
        unique_final_itinerary.append(entry)
        seen_days.add(entry["day"])

# Ensure the itinerary is sorted by day
unique_final_itinerary.sort(key=lambda x: x["day"])

# Print the final itinerary in JSON format
print(json.dumps({"itinerary": unique_final_itinerary}, indent=2))
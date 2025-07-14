# Manually constructed itinerary
itinerary = [
    {"day_range": "Day 1-5", "place": "Berlin"},
    {"day_range": "Day 6", "place": "Berlin"},
    {"day_range": "Day 6", "place": "Lyon"},
    {"day_range": "Day 7", "place": "Lyon"},
    {"day_range": "Day 7", "place": "Split"},
    {"day_range": "Day 8-10", "place": "Lyon"},
    {"day_range": "Day 9-12", "place": "Riga"},
    {"day_range": "Day 13-14", "place": "Bucharest"},
    {"day_range": "Day 15-15", "place": "Bucharest"},
    {"day_range": "Day 16-17", "place": "Lisbon"},
    {"day_range": "Day 18-21", "place": "Tallinn"}
]

# Group consecutive days in the same city
grouped_itinerary = []
current_day = None
current_city = None
for entry in itinerary:
    if entry["place"] == current_city:
        continue
    else:
        if current_city:
            start_day = grouped_itinerary[-1]["day_range"].split(" ")[1]
            end_day = entry["day_range"].split(" ")[1]
            grouped_itinerary[-1]["day_range"] = f"Day {start_day}-{end_day}"
        grouped_itinerary.append(entry)
        current_city = entry["place"]
# Add the last day range
if grouped_itinerary:
    start_day = grouped_itinerary[-1]["day_range"].split(" ")[1]
    end_day = "22"
    grouped_itinerary[-1]["day_range"] = f"Day {start_day}-{end_day}"

print({"itinerary": grouped_itinerary})
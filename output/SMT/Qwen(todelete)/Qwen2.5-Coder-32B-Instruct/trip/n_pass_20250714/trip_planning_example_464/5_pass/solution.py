# Manually construct the itinerary
itinerary = [
    {"day_range": "Day 1-5", "place": "Krakow"},
    {"day_range": "Day 6-8", "place": "Frankfurt"},
    {"day_range": "Day 9-12", "place": "Dubrovnik"},
    {"day_range": "Day 13-16", "place": "Naples"},
    {"day_range": "Day 17-18", "place": "Oslo"}
]

# Ensure the itinerary covers exactly 18 days
unique_days = set()
for entry in itinerary:
    if "-" in entry["day_range"]:
        start, end = map(int, entry["day_range"].split('-')[1].split())
        for day in range(start, end + 1):
            unique_days.add(day)
    else:
        day = int(entry["day_range"].split()[1])
        unique_days.add(day)

if len(unique_days) == 18:
    print({"itinerary": itinerary})
else:
    print("Itinerary does not cover exactly 18 days")
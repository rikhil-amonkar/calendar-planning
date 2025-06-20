cities = [
    ("Tallinn", 2),
    ("Prague", 2),
    ("Lisbon", 1),
    ("Copenhagen", 4),
    ("Dubrovnik", 4),
    ("Stockholm", 3),
    ("Split", 2),
    ("Lyon", 1)
]

itinerary = []
current_day = 1

for city, days in cities:
    end_day = current_day + days - 1
    if days == 1:
        day_range = f"Day {current_day}"
    else:
        day_range = f"Day {current_day}-{end_day}"
    itinerary.append({"day_range": day_range, "place": city})
    current_day = end_day + 1

result = {"itinerary": itinerary}
print(result)
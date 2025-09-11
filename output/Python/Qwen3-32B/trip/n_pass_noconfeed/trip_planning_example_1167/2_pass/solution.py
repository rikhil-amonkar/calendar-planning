import json

direct_flights = {
    ("Dublin", "Brussels"),
    ("Mykonos", "Naples"),
    ("Venice", "Istanbul"),
    ("Frankfurt", "Krakow"),
    ("Naples", "Dublin"),
    ("Krakow", "Brussels"),
    ("Naples", "Istanbul"),
    ("Naples", "Brussels"),
    ("Istanbul", "Frankfurt"),
    ("Brussels", "Frankfurt"),
    ("Istanbul", "Krakow"),
    ("Istanbul", "Brussels"),
    ("Venice", "Frankfurt"),
    ("Naples", "Frankfurt"),
    ("Dublin", "Frankfurt"),
    ("Venice", "Brussels"),
    ("Naples", "Venice"),
    ("Istanbul", "Dublin"),
    ("Venice", "Dublin"),
    ("Dublin", "Krakow"),
    # ✅ Added missing direct flight
    ("Frankfurt", "Brussels"),
}

cities_info = {
    "Mykonos": {"duration": 4, "fixed_start": 1},
    "Istanbul": {"duration": 3, "fixed_start": 9},
    "Dublin": {"duration": 5, "fixed_start": 11},
    "Frankfurt": {"duration": 3, "fixed_start": 15},
    "Naples": {"duration": 4},
    "Venice": {"duration": 3},
    "Brussels": {"duration": 2},
    "Krakow": {"duration": 4},
}

itinerary_order = [
    "Mykonos",
    "Naples",
    "Venice",
    "Istanbul",
    "Dublin",
    "Frankfurt",
    "Brussels",
    "Krakow",
]

itinerary = []
prev_end = 0

for city_name in itinerary_order:
    city_data = cities_info[city_name]
    if "fixed_start" in city_data:
        start = city_data["fixed_start"]
    else:
        start = prev_end
    end = start + city_data["duration"] - 1
    if itinerary:
        prev_city = itinerary[-1]["city"]
        if (prev_city, city_name) not in direct_flights:
            raise ValueError(f"No direct flight from {prev_city} to {city_name}")
    itinerary.append({"city": city_name, "start": start, "end": end})
    prev_end = end

result = {"itinerary": []}
for entry in itinerary:
    day_range = f"Day {entry['start']}-{entry['end']}"
    result["itinerary"].append({"day_range": day_range, "place": entry["city"]})

print(json.dumps(result, indent=2))
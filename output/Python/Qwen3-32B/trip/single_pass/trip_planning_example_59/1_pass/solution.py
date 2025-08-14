import json

# Define trip constraints as input variables
total_days = 16
city_durations = {
    "Bucharest": 7,
    "Lyon": 7,
    "Porto": 4
}
# Direct flights available (bidirectional)
direct_flights = [("Bucharest", "Lyon"), ("Lyon", "Porto")]
# Wedding constraint requires starting in Bucharest
cities_order = ["Bucharest", "Lyon", "Porto"]

# Calculate itinerary
itinerary = []
current_start = 1

for city in cities_order:
    duration = city_durations[city]
    end_day = current_start + duration - 1
    day_range = f"Day {current_start}-{end_day}"
    itinerary.append({"day_range": day_range, "place": city})
    current_start = end_day  # Next city starts on same day as flight

# Output result as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))
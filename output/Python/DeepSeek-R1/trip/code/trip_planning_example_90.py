import json

# Define input parameters
total_days = 17
cities = {
    "Naples": {"days": 5, "start": 1, "end": 5},
    "Vienna": {"days": 7},
    "Vilnius": {"days": 7}
}
flight_routes = {
    "Naples": ["Vienna"],
    "Vienna": ["Naples", "Vilnius"],
    "Vilnius": ["Vienna"]
}

# Calculate itinerary segments
itinerary = []
current_city = "Naples"
start_day = 1
end_day = cities[current_city]["end"]
itinerary.append({
    "day_range": f"Day {start_day}-{end_day}",
    "place": current_city
})

# Move to Vienna
current_city = "Vienna"
start_day = end_day  # Day 5
end_day = start_day + cities[current_city]["days"] - 1  # 5+7-1=11
itinerary.append({
    "day_range": f"Day {start_day}-{end_day}",
    "place": current_city
})

# Move to Vilnius
current_city = "Vilnius"
start_day = end_day  # Day 11
end_day = start_day + cities[current_city]["days"] - 1  # 11+7-1=17
itinerary.append({
    "day_range": f"Day {start_day}-{end_day}",
    "place": current_city
})

# Verify total days match
assert end_day == total_days, "Itinerary does not match total days"

# Output result
print(json.dumps({"itinerary": itinerary}))
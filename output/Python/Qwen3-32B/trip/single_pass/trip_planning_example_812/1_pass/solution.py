import json

# Define the cities and their required durations
city_durations = {
    "Porto": 3,
    "Paris": 5,
    "Florence": 3,
    "Munich": 5,
    "Warsaw": 3,
    "Nice": 5,
    "Vienna": 2
}

# Define the order of cities based on the computed itinerary
city_order = ["Porto", "Paris", "Florence", "Munich", "Warsaw", "Nice", "Vienna"]

# Compute the day ranges for each city
itinerary = []
current_day = 1
for city in city_order:
    duration = city_durations[city]
    end_day = current_day + duration - 1
    itinerary.append({
        "day_range": f"Day {current_day}-{end_day}",
        "place": city
    })
    current_day = end_day

# Output the result as a JSON-formatted dictionary
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))
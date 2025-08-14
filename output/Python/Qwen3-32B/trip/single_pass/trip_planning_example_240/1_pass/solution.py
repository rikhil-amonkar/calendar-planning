import json

# Define the cities and their required durations
cities_order = ['Prague', 'Stockholm', 'Berlin', 'Tallinn']
durations = {
    'Prague': 2,
    'Stockholm': 5,
    'Berlin': 3,
    'Tallinn': 5
}

# Calculate the itinerary
itinerary = []
current_day = 1

for city in cities_order:
    duration = durations[city]
    end_day = current_day + duration - 1
    itinerary.append({
        "day_range": f"Day {current_day}-{end_day}",
        "place": city
    })
    current_day = end_day

# Output the result as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))
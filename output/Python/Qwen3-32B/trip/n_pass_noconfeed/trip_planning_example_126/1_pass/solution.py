import json

# Define the required days per city
required_days = {
    'Krakow': 5,
    'Paris': 2,
    'Seville': 6
}

# Determine the order of cities based on constraints
cities_order = ['Krakow', 'Paris', 'Seville']

# Calculate the itinerary
current_start = 1
itinerary = []
for city in cities_order:
    days = required_days[city]
    end_day = current_start + days - 1
    day_range = f"Day {current_start}-{end_day}"
    itinerary.append({"day_range": day_range, "place": city})
    current_start = end_day

# Output as JSON
print(json.dumps({"itinerary": itinerary}))
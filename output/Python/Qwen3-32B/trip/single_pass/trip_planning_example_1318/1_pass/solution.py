import json

# Define the required durations for each city
durations = {
    'Oslo': 2,
    'Helsinki': 2,
    'Edinburgh': 3,
    'Riga': 2,
    'Tallinn': 5,
    'Budapest': 5,
    'Vilnius': 5,
    'Porto': 5,
    'Geneva': 4,
}

# Define the order of cities that satisfies all constraints and direct flight connections
order = ['Edinburgh', 'Riga', 'Tallinn', 'Vilnius', 'Helsinki', 'Budapest', 'Geneva', 'Porto', 'Oslo']

# Compute the day ranges
itinerary = []
current_day = 1

for city in order:
    duration = durations[city]
    end_day = current_day + duration - 1
    day_range = f"Day {current_day}-{end_day}"
    itinerary.append({"day_range": day_range, "place": city})
    current_day = end_day

# Output as JSON
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))
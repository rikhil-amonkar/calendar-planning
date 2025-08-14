import json
from itertools import permutations

# Define cities and their required durations
cities = {
    'Reykjavik': 7,
    'Riga': 2,
    'Warsaw': 3,
    'Istanbul': 6,
    'Krakow': 7
}

# Allowed direct flights (city: list of cities it can fly directly to)
allowed_flights = {
    'Istanbul': ['Krakow', 'Warsaw', 'Riga'],
    'Riga': ['Istanbul', 'Warsaw'],
    'Warsaw': ['Istanbul', 'Krakow', 'Riga', 'Reykjavik'],
    'Krakow': ['Istanbul', 'Warsaw'],
    'Reykjavik': ['Warsaw'],
}

# Find valid order
remaining_cities = ['Warsaw', 'Krakow', 'Reykjavik']
base_order = ['Riga', 'Istanbul']

valid_order = None
for perm in permutations(remaining_cities):
    current_order = base_order + list(perm)
    valid = True
    for i in range(len(current_order) - 1):
        current_city = current_order[i]
        next_city = current_order[i + 1]
        if next_city not in allowed_flights[current_city]:
            valid = False
            break
    if valid:
        valid_order = current_order
        break

# Generate itinerary
itinerary = []
current_start = 1
for city in valid_order:
    duration = cities[city]
    end_day = current_start + duration - 1
    day_range = f"Day {current_start}-{end_day}"
    itinerary.append({"day_range": day_range, "place": city})
    current_start = end_day  # Next city starts on this day

# Output as JSON
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))
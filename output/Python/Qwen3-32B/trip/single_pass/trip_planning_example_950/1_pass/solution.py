import itertools
import json

# Define cities and their required durations
cities_durations = {
    'Rome': 4,
    'Mykonos': 3,
    'Riga': 3,
    'Munich': 4,
    'Bucharest': 4,
    'Nice': 3,
    'Krakow': 2
}

# Direct flights adjacency list
direct_flights = {
    'Nice': ['Riga', 'Munich', 'Mykonos', 'Rome'],
    'Riga': ['Nice', 'Bucharest', 'Munich', 'Rome'],
    'Bucharest': ['Riga', 'Munich', 'Rome'],
    'Mykonos': ['Munich', 'Nice'],
    'Munich': ['Bucharest', 'Mykonos', 'Krakow', 'Nice', 'Riga'],
    'Rome': ['Nice', 'Munich', 'Mykonos', 'Bucharest', 'Riga'],
    'Krakow': ['Munich']
}

# Fixed cities with start and end days
fixed_cities = [
    {'name': 'Rome', 'start_day': 1, 'end_day': 4},
    {'name': 'Mykonos', 'start_day': 4, 'end_day': 6},
    {'name': 'Krakow', 'start_day': 16, 'end_day': 17}
]

# Remaining cities to arrange between Mykonos and Krakow
remaining_cities = ['Nice', 'Riga', 'Bucharest', 'Munich']

valid_perm = None

# Generate all permutations of the remaining cities
for perm in itertools.permutations(remaining_cities):
    # Check if the path Mykonos -> perm[0] -> perm[1] -> perm[2] -> perm[3] -> Krakow is valid
    valid = True
    current = 'Mykonos'
    for city in perm:
        if city not in direct_flights[current]:
            valid = False
            break
        current = city
    # Check if last city in perm can fly to Krakow
    if valid and 'Krakow' not in direct_flights[current]:
        valid = False
    if valid:
        valid_perm = perm
        break

if valid_perm:
    # Build the itinerary
    itinerary = [fixed_cities[0], fixed_cities[1]]  # Rome and Mykonos
    prev_end_day = fixed_cities[1]['end_day']  # 6

    for city in valid_perm:
        duration = cities_durations[city]
        start_day = prev_end_day
        end_day = start_day + duration - 1
        itinerary.append({'name': city, 'start_day': start_day, 'end_day': end_day})
        prev_end_day = end_day

    # Add Krakow
    itinerary.append(fixed_cities[2])

    # Format the itinerary for output
    formatted_itinerary = []
    for city_info in itinerary:
        day_range = f"Day {city_info['start_day']}-{city_info['end_day']}"
        formatted_itinerary.append({"day_range": day_range, "place": city_info['name']})

    # Output as JSON
    print(json.dumps({"itinerary": formatted_itinerary}, indent=2))
else:
    print(json.dumps({"error": "No valid itinerary found"}))
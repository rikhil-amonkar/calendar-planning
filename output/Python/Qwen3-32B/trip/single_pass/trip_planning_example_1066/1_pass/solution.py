import itertools
import json

# Define the cities and their required durations
cities = ['Stuttgart', 'Helsinki', 'London', 'Bucharest', 'Brussels', 'Split', 'Mykonos', 'Madrid']
durations = {
    'Stuttgart': 4,
    'Helsinki': 5,
    'London': 5,
    'Bucharest': 3,
    'Brussels': 4,
    'Split': 3,
    'Mykonos': 2,
    'Madrid': 2
}

# Define direct flights as a set of frozensets for bidirectional checking
direct_flights = {
    frozenset(('Helsinki', 'London')),
    frozenset(('Split', 'Madrid')),
    frozenset(('Helsinki', 'Madrid')),
    frozenset(('London', 'Madrid')),
    frozenset(('Brussels', 'London')),
    frozenset(('Bucharest', 'London')),
    frozenset(('Brussels', 'Bucharest')),
    frozenset(('Bucharest', 'Madrid')),
    frozenset(('Split', 'Helsinki')),
    frozenset(('Mykonos', 'Madrid')),
    frozenset(('Stuttgart', 'London')),
    frozenset(('Helsinki', 'Brussels')),
    frozenset(('Brussels', 'Madrid')),
    frozenset(('Split', 'London')),
    frozenset(('Stuttgart', 'Split')),
    frozenset(('London', 'Mykonos')),
}

# Generate all permutations of the middle cities
middle_cities = ['Helsinki', 'London', 'Bucharest', 'Brussels', 'Split', 'Mykonos']
valid_itineraries = []

for perm in itertools.permutations(middle_cities):
    itinerary = ['Stuttgart'] + list(perm) + ['Madrid']
    valid = True

    # Check direct flights between consecutive cities
    for i in range(len(itinerary) - 1):
        city_a = itinerary[i]
        city_b = itinerary[i + 1]
        if frozenset((city_a, city_b)) not in direct_flights:
            valid = False
            break

    if not valid:
        continue

    # Calculate the end day of the itinerary
    current_end_day = 0
    for i, city in enumerate(itinerary):
        if i == 0:
            start_day = 1
        else:
            start_day = current_end_day
        duration = durations[city]
        end_day = start_day + duration - 1
        current_end_day = end_day

    # Check if the end day of Madrid is 21
    if current_end_day == 21:
        valid_itineraries.append(itinerary)

# Generate the JSON output from the first valid itinerary
if valid_itineraries:
    itinerary = valid_itineraries[0]
    result = []
    current_start = 1
    for city in itinerary:
        duration = durations[city]
        end_day = current_start + duration - 1
        result.append({
            "day_range": f"Day {current_start}-{end_day}",
            "place": city
        })
        current_start = end_day  # Next city starts on the end day of the previous

    final_output = {"itinerary": result}
    print(json.dumps(final_output, indent=2))
else:
    print(json.dumps({"itinerary": []}))
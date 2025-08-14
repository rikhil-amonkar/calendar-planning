import itertools
import json

# Define the cities and their required durations
cities = ['Seville', 'Stuttgart', 'Porto', 'Madrid']
durations = {
    'Seville': 2,
    'Stuttgart': 7,
    'Porto': 3,
    'Madrid': 4
}

# Define direct flights as a set of frozensets
flights = {
    frozenset(['Porto', 'Stuttgart']),
    frozenset(['Seville', 'Porto']),
    frozenset(['Madrid', 'Porto']),
    frozenset(['Madrid', 'Seville']),
}

# Generate all permutations of the cities
for perm in itertools.permutations(cities):
    # Check if consecutive cities have direct flights
    valid = True
    for i in range(3):
        current, next_city = perm[i], perm[i+1]
        if frozenset([current, next_city]) not in flights:
            valid = False
            break
    if not valid:
        continue

    # Check if the first city is Madrid and the last is Stuttgart
    if perm[0] != 'Madrid' or perm[-1] != 'Stuttgart':
        continue

    # Calculate the start and end days for each city and check constraints
    current_start = 1
    madrid_end = None
    stuttgart_start = None
    stuttgart_end = None
    for idx, city in enumerate(perm):
        dur = durations[city]
        end_day = current_start + dur - 1

        if city == 'Madrid':
            madrid_end = end_day
        if city == 'Stuttgart':
            stuttgart_start = current_start
            stuttgart_end = end_day

        current_start = end_day  # Next city starts on this day

    # Check if the constraints are satisfied
    if madrid_end == 4 and stuttgart_start == 7 and stuttgart_end == 13:
        # Build the itinerary
        itinerary = []
        current_start = 1
        for city in perm:
            dur = durations[city]
            end_day = current_start + dur - 1
            day_range = f"Day {current_start}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city})
            current_start = end_day  # Prepare for next city
        print(json.dumps({"itinerary": itinerary}))
        exit()

# If no valid itinerary is found
print(json.dumps({"itinerary": []}))
import itertools
import json

# Define cities and their required durations
cities = ['Seville', 'Vilnius', 'Santorini', 'London', 'Stuttgart', 'Dublin', 'Frankfurt']
durations = {
    'Seville': 5,
    'Vilnius': 3,
    'Santorini': 2,
    'London': 2,
    'Stuttgart': 3,
    'Dublin': 3,
    'Frankfurt': 5
}

# Define direct flight connections as a dictionary of sets
flight_connections = {
    'Frankfurt': {'Dublin', 'London', 'Vilnius', 'Stuttgart'},
    'Dublin': {'Frankfurt', 'Seville', 'London', 'Santorini'},
    'London': {'Frankfurt', 'Dublin', 'Santorini', 'Stuttgart'},
    'Vilnius': {'Frankfurt'},
    'Stuttgart': {'Frankfurt', 'London'},
    'Seville': {'Dublin'},
    'Santorini': {'London', 'Dublin'}
}

# Generate all permutations of the cities and check for valid itineraries
for perm in itertools.permutations(cities):
    valid_transitions = True
    # Check if all consecutive cities in the permutation have direct flights
    for i in range(len(perm) - 1):
        current = perm[i]
        next_city = perm[i + 1]
        if next_city not in flight_connections[current]:
            valid_transitions = False
            break
    if not valid_transitions:
        continue

    # Calculate day ranges and check constraints for London and Stuttgart
    start_day = 1
    stuttgart_end = None
    london_end = None
    for city in perm:
        dur = durations[city]
        end_day = start_day + dur - 1
        if city == 'Stuttgart':
            stuttgart_end = end_day
        if city == 'London':
            london_end = end_day
        start_day = end_day  # Next city starts on the end day of the current city

    # Check if the constraints for London and Stuttgart are satisfied
    if stuttgart_end == 9 and london_end == 10:
        # Construct the itinerary
        itinerary = []
        start_day = 1
        for city in perm:
            dur = durations[city]
            end_day = start_day + dur - 1
            day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city})
            start_day = end_day
        # Output the result in JSON format
        print(json.dumps({"itinerary": itinerary}))
        break
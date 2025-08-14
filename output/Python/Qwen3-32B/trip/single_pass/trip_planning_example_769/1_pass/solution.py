import itertools
import json

# Define cities and their required durations
cities = {
    'Porto': 5,
    'Prague': 4,
    'Reykjavik': 4,
    'Santorini': 2,
    'Amsterdam': 2,
    'Munich': 4
}

# Define direct flight connections between cities
direct_flights = {
    'Porto': ['Amsterdam', 'Munich'],
    'Amsterdam': ['Porto', 'Munich', 'Reykjavik', 'Santorini', 'Prague'],
    'Munich': ['Porto', 'Amsterdam', 'Reykjavik', 'Prague'],
    'Reykjavik': ['Amsterdam', 'Munich', 'Prague'],
    'Santorini': ['Amsterdam'],
    'Prague': ['Reykjavik', 'Amsterdam', 'Munich']
}

# List of all cities
cities_list = ['Porto', 'Prague', 'Reykjavik', 'Santorini', 'Amsterdam', 'Munich']

# Generate all permutations of the cities and check for valid itinerary
for perm in itertools.permutations(cities_list):
    valid = True
    
    # Check if consecutive cities have direct flights
    for i in range(len(perm) - 1):
        current = perm[i]
        next_city = perm[i + 1]
        if next_city not in direct_flights[current]:
            valid = False
            break
    if not valid:
        continue
    
    # Calculate start and end days for each city in the permutation
    start_days = {}
    end_days = {}
    prev_end = 0
    for city in perm:
        duration = cities[city]
        if prev_end == 0:
            start_day = 1
        else:
            start_day = prev_end
        end_day = start_day + duration - 1
        start_days[city] = start_day
        end_days[city] = end_day
        prev_end = end_day
    
    # Check constraints for specific cities
    if (start_days['Reykjavik'] == 4 and end_days['Reykjavik'] == 7 and
        start_days['Munich'] == 7 and end_days['Munich'] == 10 and
        start_days['Amsterdam'] == 14 and end_days['Amsterdam'] == 15):
        # Build the itinerary
        itinerary = []
        for city in perm:
            start = start_days[city]
            end = end_days[city]
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
        print(json.dumps({"itinerary": itinerary}))
        exit()
import itertools
import json

# Define the cities and their required durations
cities = ['Prague', 'Stuttgart', 'Split', 'Krakow', 'Florence']
durations = {
    'Prague': 4,
    'Stuttgart': 2,
    'Split': 2,
    'Krakow': 2,
    'Florence': 2
}

# Define direct flights between cities
direct_flights = {
    'Stuttgart': ['Split', 'Krakow'],
    'Prague': ['Florence', 'Krakow', 'Split'],
    'Split': ['Stuttgart', 'Krakow', 'Prague'],
    'Krakow': ['Stuttgart', 'Split', 'Prague'],
    'Florence': ['Prague']
}

# Generate all permutations of the cities
for perm in itertools.permutations(cities):
    valid = True
    for i in range(len(perm) - 1):
        current = perm[i]
        next_city = perm[i + 1]
        if next_city not in direct_flights[current]:
            valid = False
            break
    if not valid:
        continue

    # Calculate start and end days for each city in the sequence
    start_days = {}
    end_days = {}
    current_start = 1
    for city in perm:
        duration = durations[city]
        end = current_start + duration
        start_days[city] = current_start
        end_days[city] = end
        current_start = end

    # Check if total days is exactly 8
    total_days = end_days[perm[-1]]
    if total_days != 8:
        continue

    # Check if the events are satisfied
    # Wedding in Stuttgart between day 2 and 3
    stuttgart_days = list(range(start_days.get('Stuttgart', 0), end_days.get('Stuttgart', 0)))
    if 'Stuttgart' in perm and not (2 in stuttgart_days and 3 in stuttgart_days):
        continue

    # Meeting in Split between day 3 and 4
    split_days = list(range(start_days.get('Split', 0), end_days.get('Split', 0)))
    if 'Split' in perm and not (3 in split_days and 4 in split_days):
        continue

    # Build the itinerary
    itinerary = []
    current_start = 1
    for city in perm:
        duration = durations[city]
        end = current_start + duration
        day_range = f"Day {current_start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
        current_start = end

    print(json.dumps({"itinerary": itinerary}))
    break
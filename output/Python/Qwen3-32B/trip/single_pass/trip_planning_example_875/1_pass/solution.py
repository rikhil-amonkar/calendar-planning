import itertools
import json

# Define the cities and their required durations
cities = ['Stuttgart', 'Edinburgh', 'Athens', 'Split', 'Krakow', 'Venice', 'Mykonos']
durations = {
    'Stuttgart': 3,
    'Edinburgh': 4,
    'Athens': 4,
    'Split': 2,
    'Krakow': 4,
    'Venice': 5,
    'Mykonos': 4,
}

# Define the direct flight connections
direct_flights = {
    'Stuttgart': ['Krakow', 'Edinburgh', 'Venice', 'Athens', 'Split'],
    'Edinburgh': ['Krakow', 'Stuttgart', 'Venice', 'Athens'],
    'Krakow': ['Stuttgart', 'Split', 'Edinburgh'],
    'Split': ['Krakow', 'Athens'],
    'Athens': ['Split', 'Mykonos', 'Stuttgart', 'Venice', 'Edinburgh'],
    'Venice': ['Stuttgart', 'Edinburgh', 'Athens'],
    'Mykonos': ['Athens'],
}

# Generate all permutations of cities
for perm in itertools.permutations(cities):
    valid_path = True
    # Check if each consecutive pair has a direct flight
    for i in range(len(perm) - 1):
        current = perm[i]
        next_city = perm[i + 1]
        if next_city not in direct_flights[current]:
            valid_path = False
            break
    if not valid_path:
        continue

    # Calculate day ranges for each city in the permutation
    day_ranges = []
    current_day_start = 1
    for city in perm:
        dur = durations[city]
        end_day = current_day_start + dur - 1
        day_ranges.append((current_day_start, end_day))
        current_day_start = end_day

    # Check constraints for each city with specific time requirements
    constraint_ok = True

    # Check Stuttgart (must include days 11, 12, or 13)
    stuttgart_idx = perm.index('Stuttgart')
    stuttgart_start, stuttgart_end = day_ranges[stuttgart_idx]
    if not any(stuttgart_start <= d <= stuttgart_end for d in [11, 12, 13]):
        constraint_ok = False

    # Check Split (must include days 13 or 14)
    split_idx = perm.index('Split')
    split_start, split_end = day_ranges[split_idx]
    if not any(split_start <= d <= split_end for d in [13, 14]):
        constraint_ok = False

    # Check Krakow (must include days 8, 9, 10, or 11)
    krakow_idx = perm.index('Krakow')
    krakow_start, krakow_end = day_ranges[krakow_idx]
    if not any(krakow_start <= d <= krakow_end for d in [8, 9, 10, 11]):
        constraint_ok = False

    if constraint_ok:
        # Construct the itinerary
        itinerary = []
        for i in range(len(perm)):
            city = perm[i]
            start, end = day_ranges[i]
            day_range_str = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range_str, "place": city})
        print(json.dumps({"itinerary": itinerary}, indent=2))
        exit()
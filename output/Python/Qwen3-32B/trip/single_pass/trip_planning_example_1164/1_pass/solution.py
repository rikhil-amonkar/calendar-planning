import itertools
import json
from collections import defaultdict

# Define the cities and their required durations
cities = ['Reykjavik', 'Stockholm', 'Porto', 'Nice', 'Venice', 'Vienna', 'Split', 'Copenhagen']
durations = {
    'Reykjavik': 2,
    'Stockholm': 2,
    'Porto': 5,
    'Nice': 3,
    'Venice': 4,
    'Vienna': 3,
    'Split': 3,
    'Copenhagen': 2
}

# Define direct flights as bidirectional connections
direct_flights = [
    ('Copenhagen', 'Vienna'),
    ('Nice', 'Stockholm'),
    ('Split', 'Copenhagen'),
    ('Nice', 'Reykjavik'),
    ('Nice', 'Porto'),
    ('Reykjavik', 'Vienna'),
    ('Stockholm', 'Copenhagen'),
    ('Nice', 'Venice'),
    ('Nice', 'Vienna'),
    ('Reykjavik', 'Copenhagen'),
    ('Nice', 'Copenhagen'),
    ('Stockholm', 'Vienna'),
    ('Venice', 'Vienna'),
    ('Copenhagen', 'Porto'),
    ('Reykjavik', 'Stockholm'),
    ('Stockholm', 'Split'),
    ('Split', 'Vienna'),
    ('Copenhagen', 'Venice'),
    ('Vienna', 'Porto'),
]

# Build an adjacency list for the flight graph
graph = defaultdict(set)
for a, b in direct_flights:
    graph[a].add(b)
    graph[b].add(a)

def compute_start_days(order, durations):
    """Calculate the start day for each city in the given order."""
    n = len(order)
    start_days = [0] * n
    start_days[0] = 1
    for i in range(1, n):
        prev_city = order[i-1]
        start_days[i] = start_days[i-1] + durations[prev_city] - 1
    return start_days

# Iterate through all possible permutations of the cities
for perm in itertools.permutations(cities):
    # Check if all consecutive cities have a direct flight
    valid = True
    for i in range(len(perm) - 1):
        if perm[i+1] not in graph[perm[i]]:
            valid = False
            break
    if not valid:
        continue

    start_days = compute_start_days(perm, durations)

    # Check constraints for specific cities
    reykjavik_idx = perm.index('Reykjavik')
    reykjavik_start = start_days[reykjavik_idx]
    if reykjavik_start not in {2, 3}:
        continue

    stockholm_idx = perm.index('Stockholm')
    stockholm_start = start_days[stockholm_idx]
    if stockholm_start not in {3, 4}:
        continue

    porto_idx = perm.index('Porto')
    porto_start = start_days[porto_idx]
    if porto_start != 13:
        continue

    vienna_idx = perm.index('Vienna')
    vienna_start = start_days[vienna_idx]
    if vienna_start != 11:
        continue

    # Construct the itinerary
    itinerary = []
    for i in range(len(perm)):
        city = perm[i]
        start = start_days[i]
        duration = durations[city]
        end = start + duration - 1
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})

    # Output the result as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
    exit()

print(json.dumps({"error": "No valid itinerary found."}))
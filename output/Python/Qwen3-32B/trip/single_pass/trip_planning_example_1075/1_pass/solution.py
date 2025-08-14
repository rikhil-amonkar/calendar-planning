import itertools
import json

# Define cities and their required durations
cities = {
    'Vienna': 4,
    'Lyon': 3,
    'Edinburgh': 4,
    'Reykjavik': 5,
    'Stuttgart': 5,
    'Manchester': 2,
    'Split': 5,
    'Prague': 4
}

# Define direct flights as adjacency list
flights = {
    'Reykjavik': ['Stuttgart', 'Vienna'],
    'Stuttgart': ['Reykjavik', 'Split', 'Vienna', 'Edinburgh', 'Manchester'],
    'Split': ['Stuttgart', 'Lyon', 'Manchester', 'Prague'],
    'Manchester': ['Split', 'Prague', 'Vienna'],
    'Prague': ['Manchester', 'Edinburgh', 'Vienna', 'Split', 'Lyon', 'Reykjavik'],
    'Edinburgh': ['Prague', 'Stuttgart'],
    'Vienna': ['Stuttgart', 'Reykjavik', 'Manchester', 'Prague', 'Split', 'Lyon'],
    'Lyon': ['Vienna', 'Prague', 'Split']
}

# Generate all permutations of the cities
for perm in itertools.permutations(cities.keys()):
    # Calculate start days for each city in the permutation
    start_days = [1]
    for i in range(1, len(perm)):
        prev_duration = cities[perm[i-1]]
        start_day = start_days[-1] + prev_duration - 1
        start_days.append(start_day)
    
    # Check if Edinburgh is in the correct position (start day 5)
    try:
        edinburgh_idx = perm.index('Edinburgh')
        if start_days[edinburgh_idx] != 5:
            continue
    except ValueError:
        continue  # Edinburgh not in permutation (shouldn't happen)
    
    # Check if Split is in the correct position (start day 19)
    try:
        split_idx = perm.index('Split')
        if start_days[split_idx] != 19:
            continue
    except ValueError:
        continue  # Split not in permutation (shouldn't happen)
    
    # Check all consecutive transitions are valid flights
    valid_transitions = True
    for i in range(len(perm) - 1):
        current = perm[i]
        next_city = perm[i+1]
        if next_city not in flights[current]:
            valid_transitions = False
            break
    if not valid_transitions:
        continue
    
    # Build the itinerary
    itinerary = []
    for i in range(len(perm)):
        city = perm[i]
        duration = cities[city]
        start = start_days[i]
        end = start + duration - 1
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Output the result as JSON
    print(json.dumps({"itinerary": itinerary}))
    break
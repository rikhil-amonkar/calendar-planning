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

# Define direct flights as a set of bidirectional pairs
direct_flights = {
    ('Reykjavik', 'Stuttgart'),
    ('Stuttgart', 'Split'),
    ('Stuttgart', 'Vienna'),
    ('Prague', 'Manchester'),
    ('Edinburgh', 'Prague'),
    ('Manchester', 'Split'),
    ('Prague', 'Vienna'),
    ('Vienna', 'Manchester'),
    ('Prague', 'Split'),
    ('Vienna', 'Lyon'),
    ('Stuttgart', 'Edinburgh'),
    ('Split', 'Lyon'),
    ('Stuttgart', 'Manchester'),
    ('Prague', 'Lyon'),
    ('Reykjavik', 'Vienna'),
    ('Prague', 'Reykjavik'),
    ('Vienna', 'Split'),
}

# Create a set of all directed edges (both directions)
direct_edges = set()
for a, b in direct_flights:
    direct_edges.add((a, b))
    direct_edges.add((b, a))

# Function to compute start days for a permutation
def compute_start_days(perm, durations):
    start_days = [1]  # start day of first city is 1
    for i in range(1, len(perm)):
        prev_city = perm[i-1]
        start_prev = start_days[i-1]
        duration_prev = durations[prev_city]
        # start day of current city is end day of previous city
        start_current = start_prev + duration_prev - 1
        start_days.append(start_current)
    return start_days

# Iterate through all permutations
for perm in itertools.permutations(cities.keys()):
    # Check if consecutive cities have direct flights
    valid = True
    for i in range(len(perm)-1):
        if (perm[i], perm[i+1]) not in direct_edges:
            valid = False
            break
    if not valid:
        continue

    # Compute start days
    start_days = compute_start_days(perm, cities)
    
    # Check Edinburgh's start day is 5
    edinburgh_index = perm.index('Edinburgh')
    edinburgh_start = start_days[edinburgh_index]
    if edinburgh_start != 5:
        continue

    # Check Split's start day is 19
    split_index = perm.index('Split')
    split_start = start_days[split_index]
    if split_start != 19:
        continue

    # If all conditions are met, build the itinerary
    itinerary = []
    for i in range(len(perm)):
        city = perm[i]
        start = start_days[i]
        duration = cities[city]
        end = start + duration - 1
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})

    # Output the JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
    exit()

# If no itinerary found
print(json.dumps({"itinerary": []}))
import itertools
import json

# Define cities and their durations
cities = ['Helsinki', 'Warsaw', 'Madrid', 'Split', 'Reykjavik', 'Budapest']
durations = {
    'Helsinki': 2,
    'Warsaw': 3,
    'Madrid': 4,
    'Split': 4,
    'Reykjavik': 2,
    'Budapest': 4
}

# Define direct flights (both directions included)
direct_flights = {
    ('Helsinki', 'Reykjavik'), ('Reykjavik', 'Helsinki'),
    ('Budapest', 'Warsaw'), ('Warsaw', 'Budapest'),
    ('Madrid', 'Split'), ('Split', 'Madrid'),
    ('Helsinki', 'Split'), ('Split', 'Helsinki'),
    ('Helsinki', 'Madrid'), ('Madrid', 'Helsinki'),
    ('Helsinki', 'Budapest'), ('Budapest', 'Helsinki'),
    ('Reykjavik', 'Warsaw'), ('Warsaw', 'Reykjavik'),
    ('Helsinki', 'Warsaw'), ('Warsaw', 'Helsinki'),
    ('Madrid', 'Budapest'), ('Budapest', 'Madrid'),
    ('Budapest', 'Reykjavik'), ('Reykjavik', 'Budapest'),
    ('Madrid', 'Warsaw'), ('Warsaw', 'Madrid'),
    ('Warsaw', 'Split'), ('Split', 'Warsaw'),
    ('Reykjavik', 'Madrid'), ('Madrid', 'Reykjavik'),
}

# Generate all permutations starting with Helsinki
for perm in itertools.permutations(cities):
    if perm[0] != 'Helsinki':
        continue
    valid = True
    # Check direct flights between consecutive cities
    for i in range(len(perm) - 1):
        if (perm[i], perm[i+1]) not in direct_flights:
            valid = False
            break
    if not valid:
        continue
    # Calculate start and end days for each city
    start_days = [1]  # Helsinki starts on day 1
    end_days = [1 + durations[perm[0]] - 1]
    for i in range(1, len(perm)):
        start = end_days[-1]
        end = start + durations[perm[i]] - 1
        start_days.append(start)
        end_days.append(end)
    # Check if Reykjavik starts on day 8 and Warsaw starts on day 9
    reykjavik_idx = perm.index('Reykjavik')
    war_idx = perm.index('Warsaw')
    if start_days[reykjavik_idx] == 8 and start_days[war_idx] == 9:
        # Check total days is 14
        if end_days[-1] == 14:
            # Found valid itinerary
            itinerary = []
            for i in range(len(perm)):
                start = start_days[i]
                end = end_days[i]
                day_range = f"Day {start}-Day {end}"
                itinerary.append({"day_range": day_range, "place": perm[i]})
            print(json.dumps({"itinerary": itinerary}))
            exit()
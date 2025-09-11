import itertools
import json

cities = ['Riga', 'Manchester', 'Bucharest', 'Florence', 'Vienna', 'Istanbul', 'Reykjavik', 'Stuttgart']

durations = {
    'Riga': 4,
    'Manchester': 5,
    'Bucharest': 4,
    'Florence': 4,
    'Vienna': 2,
    'Istanbul': 2,
    'Reykjavik': 4,
    'Stuttgart': 5
}

direct_flights = {
    # Original pairs
    ('Bucharest', 'Vienna'),
    ('Reykjavik', 'Vienna'),
    ('Manchester', 'Vienna'),
    ('Manchester', 'Riga'),
    ('Riga', 'Vienna'),
    ('Istanbul', 'Vienna'),
    ('Vienna', 'Florence'),
    ('Stuttgart', 'Vienna'),
    ('Riga', 'Bucharest'),
    ('Istanbul', 'Riga'),
    ('Stuttgart', 'Istanbul'),
    ('Reykjavik', 'Stuttgart'),
    ('Istanbul', 'Bucharest'),
    ('Manchester', 'Istanbul'),
    ('Manchester', 'Bucharest'),
    ('Stuttgart', 'Manchester'),
    # Reverse pairs
    ('Vienna', 'Bucharest'),
    ('Vienna', 'Reykjavik'),
    ('Vienna', 'Manchester'),
    ('Riga', 'Manchester'),
    ('Vienna', 'Riga'),
    ('Vienna', 'Istanbul'),
    ('Florence', 'Vienna'),
    ('Vienna', 'Stuttgart'),
    ('Bucharest', 'Riga'),
    ('Riga', 'Istanbul'),
    ('Istanbul', 'Stuttgart'),
    ('Stuttgart', 'Reykjavik'),
    ('Bucharest', 'Istanbul'),
    ('Istanbul', 'Manchester'),
    ('Bucharest', 'Manchester'),
    ('Manchester', 'Stuttgart'),
}

for perm in itertools.permutations(cities):
    # Check transitions between consecutive cities
    valid_transitions = True
    for i in range(len(perm) - 1):
        c1 = perm[i]
        c2 = perm[i+1]
        if (c1, c2) not in direct_flights:
            valid_transitions = False
            break
    if not valid_transitions:
        continue

    # Compute start days for each city in permutation
    start_days = []
    current_start = 1
    for city in perm:
        start_days.append(current_start)
        duration = durations[city]
        current_start += duration - 1

    # Check if Istanbul's start day is 12 and Bucharest's is 16
    ist_pos = perm.index('Istanbul')
    buch_pos = perm.index('Bucharest')
    if start_days[ist_pos] == 12 and start_days[buch_pos] == 16:
        # Found valid permutation
        itinerary = []
        for i, city in enumerate(perm):
            start = start_days[i]
            duration = durations[city]
            end = start + duration - 1
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
        # Output JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
        exit()
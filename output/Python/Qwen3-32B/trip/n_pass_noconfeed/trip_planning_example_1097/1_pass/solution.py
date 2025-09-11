import itertools
import json

# Define the cities and their required durations
cities = {
    'Reykjavik': 4,
    'Riga': 2,
    'Oslo': 3,
    'Lyon': 5,
    'Dubrovnik': 2,
    'Madrid': 2,
    'Warsaw': 4,
    'London': 3
}

# Define the events: (start_day, end_day)
events = {
    'Riga': (4, 5),
    'Dubrovnik': (7, 8)
}

# Define the direct flights as a set of tuples (city1, city2)
direct_flights = {
    ('Warsaw', 'Reykjavik'), ('Reykjavik', 'Warsaw'),
    ('Oslo', 'Madrid'), ('Madrid', 'Oslo'),
    ('Warsaw', 'Riga'), ('Riga', 'Warsaw'),
    ('Lyon', 'London'), ('London', 'Lyon'),
    ('Madrid', 'London'), ('London', 'Madrid'),
    ('Warsaw', 'London'), ('London', 'Warsaw'),
    ('Reykjavik', 'Madrid'), ('Madrid', 'Reykjavik'),
    ('Warsaw', 'Oslo'), ('Oslo', 'Warsaw'),
    ('Oslo', 'Dubrovnik'), ('Dubrovnik', 'Oslo'),
    ('Oslo', 'Reykjavik'), ('Reykjavik', 'Oslo'),
    ('Riga', 'Oslo'), ('Oslo', 'Riga'),
    ('Oslo', 'Lyon'), ('Lyon', 'Oslo'),
    ('Oslo', 'London'), ('London', 'Oslo'),
    ('London', 'Reykjavik'), ('Reykjavik', 'London'),
    ('Warsaw', 'Madrid'), ('Madrid', 'Warsaw'),
    ('Madrid', 'Lyon'), ('Lyon', 'Madrid'),
    ('Dubrovnik', 'Madrid'), ('Madrid', 'Dubrovnik')
}

city_list = list(cities.keys())

for perm in itertools.permutations(city_list):
    start_days = [1]
    end_days = [start_days[0] + cities[perm[0]] - 1]
    valid = True

    for i in range(1, len(perm)):
        start_day = end_days[i-1]
        duration = cities[perm[i]]
        end_day = start_day + duration - 1
        start_days.append(start_day)
        end_days.append(end_day)

    total_days = end_days[-1]
    if total_days != 18:
        continue

    # Check Riga's event
    riga_index = perm.index('Riga')
    if start_days[riga_index] != 4 or end_days[riga_index] != 5:
        continue

    # Check Dubrovnik's event
    dubrovnik_index = perm.index('Dubrovnik')
    if start_days[dubrovnik_index] != 7 or end_days[dubrovnik_index] != 8:
        continue

    # Check direct flights between consecutive cities
    for i in range(len(perm) - 1):
        city_a = perm[i]
        city_b = perm[i+1]
        if (city_a, city_b) not in direct_flights:
            valid = False
            break
    if not valid:
        continue

    # Construct the itinerary
    itinerary = []
    for i in range(len(perm)):
        start = start_days[i]
        end = end_days[i]
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": perm[i]})

    print(json.dumps({"itinerary": itinerary}))
    exit()

print(json.dumps({"itinerary": []}))
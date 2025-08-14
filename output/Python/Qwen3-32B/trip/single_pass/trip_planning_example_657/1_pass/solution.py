import itertools
import json

cities = ['Frankfurt', 'Manchester', 'Valencia', 'Naples', 'Oslo', 'Vilnius']
durations = {
    'Frankfurt': 4,
    'Manchester': 4,
    'Valencia': 4,
    'Naples': 4,
    'Oslo': 3,
    'Vilnius': 2
}

adjacency = {
    'Frankfurt': {'Valencia', 'Manchester', 'Naples', 'Oslo', 'Vilnius'},
    'Manchester': {'Frankfurt', 'Naples', 'Oslo'},
    'Valencia': {'Frankfurt', 'Naples'},
    'Naples': {'Frankfurt', 'Manchester', 'Oslo', 'Valencia'},
    'Oslo': {'Frankfurt', 'Vilnius', 'Manchester', 'Naples'},
    'Vilnius': {'Frankfurt', 'Oslo'}
}

for perm in itertools.permutations(cities):
    valid = True
    for i in range(len(perm) - 1):
        current = perm[i]
        next_city = perm[i + 1]
        if next_city not in adjacency[current]:
            valid = False
            break
    if not valid:
        continue

    vilnius_start = None
    frankfurt_start = None
    start_day = 1
    for city in perm:
        duration = durations[city]
        if city == 'Vilnius':
            vilnius_start = start_day
        elif city == 'Frankfurt':
            frankfurt_start = start_day
        end_day = start_day + duration - 1
        start_day = end_day

    if vilnius_start == 12 and frankfurt_start == 13:
        itinerary = []
        current_start = 1
        for city in perm:
            duration = durations[city]
            end = current_start + duration - 1
            day_range = f"Day {current_start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
            current_start = end
        print(json.dumps({"itinerary": itinerary}))
        exit()

print(json.dumps({"itinerary": []}))
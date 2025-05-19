import json
from itertools import permutations

cities = {
    'Reykjavik': 7,
    'Riga': 2,
    'Warsaw': 3,
    'Istanbul': 6,
    'Krakow': 7
}

direct_flights = {
    'Istanbul': ['Krakow', 'Warsaw', 'Riga'],
    'Krakow': ['Istanbul', 'Warsaw'],
    'Warsaw': ['Istanbul', 'Krakow', 'Riga', 'Reykjavik'],
    'Riga': ['Istanbul', 'Warsaw'],
    'Reykjavik': ['Warsaw']
}

for perm in permutations(cities.keys()):
    valid = True
    for i in range(len(perm)-1):
        if perm[i+1] not in direct_flights[perm[i]]:
            valid = False
            break
    if not valid:
        continue
    
    day_ranges = []
    current_day = 1
    for idx, city in enumerate(perm):
        duration = cities[city]
        if idx == 0:
            start = current_day
            end = start + duration - 1
        else:
            start = current_day
            end = start + duration - 1
        day_ranges.append((city, start, end))
        current_day = end
    
    total_transitions = len(perm) - 1
    if sum(cities.values()) - total_transitions != 21:
        continue
    
    riga_valid = False
    istanbul_valid = False
    for city, start, end in day_ranges:
        if city == 'Riga':
            if start <= 1 and end >= 2:
                riga_valid = True
        if city == 'Istanbul':
            if start <= 2 and end >= 7:
                istanbul_valid = True
    
    if riga_valid and istanbul_valid:
        itinerary = []
        for city, start, end in day_ranges:
            day_range = f"Day {start}-{end}" if start != end else f"Day {start}"
            itinerary.append({"day_range": day_range, "place": city})
        print(json.dumps({"itinerary": itinerary}))
        exit()

print(json.dumps({"itinerary": []}))
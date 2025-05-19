import json
import itertools

cities = {
    'Hamburg': {'days': 5},
    'Frankfurt': {'days': 2, 'event': (5, 6)},
    'Geneva': {'days': 3},
    'Mykonos': {'days': 3, 'event': (10, 12)},
    'Naples': {'days': 5},
    'Manchester': {'days': 4, 'event': (15, 18)},
    'Porto': {'days': 2}
}

flight_graph = {
    'Hamburg': ['Frankfurt', 'Porto', 'Geneva', 'Manchester'],
    'Frankfurt': ['Hamburg', 'Geneva', 'Porto', 'Naples', 'Manchester'],
    'Porto': ['Hamburg', 'Frankfurt', 'Geneva', 'Manchester'],
    'Geneva': ['Mykonos', 'Frankfurt', 'Porto', 'Manchester', 'Naples'],
    'Mykonos': ['Naples', 'Geneva'],
    'Naples': ['Mykonos', 'Manchester', 'Frankfurt', 'Geneva'],
    'Manchester': ['Geneva', 'Naples', 'Frankfurt', 'Porto', 'Hamburg']
}

found = False
for perm in itertools.permutations(cities.keys()):
    if len(set(perm)) != 7:
        continue
    
    valid = True
    for i in range(len(perm)-1):
        if perm[i+1] not in flight_graph[perm[i]]:
            valid = False
            break
    if not valid:
        continue
    
    day_ranges = []
    previous_end = 0
    for i, city in enumerate(perm):
        days_needed = cities[city]['days']
        if i == 0:
            start = 1
            end = start + days_needed - 1
        else:
            start = previous_end
            end = start + days_needed - 1
        day_ranges.append((start, end, city))
        previous_end = end
    
    if previous_end > 18:
        continue
    
    valid_days = True
    for start, end, city in day_ranges:
        if end - start + 1 != cities[city]['days']:
            valid_days = False
            break
        if 'event' in cities[city]:
            event_start, event_end = cities[city]['event']
            if not (start <= event_end and end >= event_start):
                valid_days = False
                break
    if not valid_days:
        continue
    
    formatted = []
    for start, end, city in day_ranges:
        day_range = f"Day {start}-{end}" if start != end else f"Day {start}"
        formatted.append({"day_range": day_range, "place": city})
    
    print(json.dumps({"itinerary": formatted}))
    found = True
    break

if not found:
    print(json.dumps({"itinerary": []}))
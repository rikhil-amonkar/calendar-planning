import itertools
import json

cities = {
    'Reykjavik': 2,
    'Stockholm': 3,
    'Oslo': 5,
    'Stuttgart': 5,
    'Split': 3,
    'Geneva': 2,
    'Porto': 3,
    'Tallinn': 5
}

direct_flights = {
    'Reykjavik': ['Stuttgart', 'Stockholm', 'Tallinn', 'Oslo'],
    'Stuttgart': ['Reykjavik', 'Stockholm', 'Porto', 'Split'],
    'Stockholm': ['Reykjavik', 'Oslo', 'Stuttgart', 'Split', 'Geneva'],
    'Oslo': ['Reykjavik', 'Stockholm', 'Split', 'Geneva', 'Porto', 'Tallinn'],
    'Split': ['Oslo', 'Stuttgart', 'Geneva'],
    'Geneva': ['Oslo', 'Stockholm', 'Split', 'Porto'],
    'Porto': ['Stuttgart', 'Oslo', 'Geneva'],
    'Tallinn': ['Reykjavik', 'Oslo']
}

remaining_cities = ['Stockholm', 'Oslo', 'Stuttgart', 'Split', 'Geneva', 'Porto', 'Tallinn']

for perm in itertools.permutations(remaining_cities):
    # Check if consecutive cities have direct flights
    valid = True
    path = ['Reykjavik'] + list(perm)
    for i in range(1, len(path)):
        prev_city = path[i-1]
        curr_city = path[i]
        if curr_city not in direct_flights[prev_city]:
            valid = False
            break
    if not valid:
        continue

    # Compute start and end days
    start_days = {}
    end_days = {}
    current_day = 1  # start_day for Reykjavik is 1
    duration = cities['Reykjavik']
    end_day = current_day + duration - 1
    start_days['Reykjavik'] = current_day
    end_days['Reykjavik'] = end_day
    current_day = end_day  # next city starts on this day

    for city in perm:
        start_days[city] = current_day
        duration = cities[city]
        end_day = current_day + duration - 1
        end_days[city] = end_day
        current_day = end_day

    # Check constraints
    # Check Stockholm's start_day is <=4
    if 'Stockholm' in perm:
        stock_start = start_days['Stockholm']
        if stock_start > 4:
            continue

    # Check Porto's start_day is 19
    if 'Porto' in perm:
        porto_start = start_days['Porto']
        if porto_start != 19:
            continue

    # If all checks passed, build the itinerary
    itinerary = []
    for city in path:
        start = start_days[city]
        end = end_days[city]
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})

    print(json.dumps({"itinerary": itinerary}, indent=2))
    exit()
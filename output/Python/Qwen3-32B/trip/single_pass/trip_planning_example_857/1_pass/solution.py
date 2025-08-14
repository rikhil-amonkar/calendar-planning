import itertools
import json

cities = {
    'Porto': 2,
    'Geneva': 3,
    'Mykonos': 3,
    'Manchester': 4,
    'Hamburg': 5,
    'Naples': 5,
    'Frankfurt': 2
}

flights = {
    'Hamburg': ['Frankfurt', 'Porto', 'Geneva', 'Manchester'],
    'Frankfurt': ['Hamburg', 'Geneva', 'Porto', 'Naples', 'Manchester'],
    'Geneva': ['Frankfurt', 'Porto', 'Mykonos', 'Manchester', 'Hamburg'],
    'Mykonos': ['Geneva', 'Naples'],
    'Naples': ['Mykonos', 'Manchester', 'Frankfurt', 'Geneva'],
    'Manchester': ['Geneva', 'Naples', 'Frankfurt', 'Porto', 'Hamburg'],
    'Porto': ['Hamburg', 'Frankfurt', 'Geneva', 'Manchester'],
}

cities_list = list(cities.keys())

for perm in itertools.permutations(cities_list):
    valid = True
    for i in range(len(perm) - 1):
        current = perm[i]
        next_city = perm[i + 1]
        if next_city not in flights[current]:
            valid = False
            break
    if not valid:
        continue

    start_day = 1
    city_days = []
    for city in perm:
        duration = cities[city]
        end_day = start_day + duration - 1
        city_days.append((city, start_day, end_day))
        start_day = end_day

    mykonos_ok = False
    for city, s, e in city_days:
        if city == 'Mykonos':
            if not (e < 10 or s > 12):
                mykonos_ok = True
                break
    if not mykonos_ok:
        continue

    manchester_ok = False
    for city, s, e in city_days:
        if city == 'Manchester':
            if not (e < 15 or s > 18):
                manchester_ok = True
                break
    if not manchester_ok:
        continue

    frankfurt_ok = False
    for city, s, e in city_days:
        if city == 'Frankfurt':
            if not (e < 5 or s > 6):
                frankfurt_ok = True
                break
    if not frankfurt_ok:
        continue

    itinerary = []
    for city, s, e in city_days:
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})

    print(json.dumps({"itinerary": itinerary}))
    exit()
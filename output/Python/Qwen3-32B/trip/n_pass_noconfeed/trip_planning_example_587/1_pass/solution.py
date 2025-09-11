import itertools
import json

cities = ['Manchester', 'Istanbul', 'Venice', 'Krakow', 'Lyon']
city_durations = {
    'Manchester': 3,
    'Istanbul': 7,
    'Venice': 7,
    'Krakow': 6,
    'Lyon': 2
}

direct_flight_pairs = [
    ('Manchester', 'Venice'),
    ('Manchester', 'Istanbul'),
    ('Manchester', 'Krakow'),
    ('Venice', 'Istanbul'),
    ('Istanbul', 'Krakow'),
    ('Venice', 'Lyon'),
    ('Lyon', 'Istanbul'),
]

direct_flights = set()
for a, b in direct_flight_pairs:
    direct_flights.add((a, b))
    direct_flights.add((b, a))

remaining_cities = [city for city in cities if city != 'Manchester']

for perm in itertools.permutations(remaining_cities):
    sequence = ['Manchester'] + list(perm)
    valid_transitions = True
    for i in range(len(sequence) - 1):
        a, b = sequence[i], sequence[i + 1]
        if (a, b) not in direct_flights:
            valid_transitions = False
            break
    if not valid_transitions:
        continue

    current_day = 1
    day_ranges = []
    for city in sequence:
        days = city_durations[city]
        end_day = current_day + days - 1
        day_ranges.append((current_day, end_day, city))
        current_day = end_day

    venice_start = None
    venice_end = None
    for start, end, city in day_ranges:
        if city == 'Venice':
            venice_start = start
            venice_end = end
    overlap = (venice_start <= 9) and (venice_end >= 3)
    if not overlap:
        continue

    itinerary = []
    for start, end, city in day_ranges:
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})

    print(json.dumps({"itinerary": itinerary}))
    exit()

print(json.dumps({"itinerary": []}))
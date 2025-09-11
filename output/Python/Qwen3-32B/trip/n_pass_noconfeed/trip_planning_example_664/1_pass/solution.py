import itertools
import json

cities = ['Tallinn', 'Bucharest', 'Seville', 'Stockholm', 'Munich', 'Milan']

city_durations = {
    'Tallinn': 2,
    'Bucharest': 4,
    'Seville': 5,
    'Stockholm': 5,
    'Munich': 5,
    'Milan': 2
}

event_constraints = {
    'Bucharest': {'start': 1, 'end': 4},
    'Munich': {'start': 4, 'end': 8},
    'Seville': {'start': 8, 'end': 12}
}

flight_connections = {
    ('Milan', 'Stockholm'),
    ('Munich', 'Stockholm'),
    ('Bucharest', 'Munich'),
    ('Munich', 'Seville'),
    ('Stockholm', 'Tallinn'),
    ('Munich', 'Milan'),
    ('Munich', 'Tallinn'),
    ('Seville', 'Milan')
}

for perm in itertools.permutations(cities):
    valid_flight = True
    for i in range(len(perm) - 1):
        city_a, city_b = perm[i], perm[i+1]
        if (city_a, city_b) not in flight_connections and (city_b, city_a) not in flight_connections:
            valid_flight = False
            break
    if not valid_flight:
        continue

    day_ranges = {}
    current_start = 1
    for city in perm:
        duration = city_durations[city]
        end = current_start + duration - 1
        day_ranges[city] = (current_start, end)
        current_start = end

    valid_event = True
    for city in event_constraints:
        event_start = event_constraints[city]['start']
        event_end = event_constraints[city]['end']
        city_start, city_end = day_ranges[city]
        if not (city_start <= event_start and city_end >= event_end):
            valid_event = False
            break
    if valid_event:
        itinerary = []
        current_start = 1
        for city in perm:
            duration = city_durations[city]
            end = current_start + duration - 1
            day_range_str = f"Day {current_start}-{end}"
            itinerary.append({"day_range": day_range_str, "place": city})
            current_start = end
        print(json.dumps({"itinerary": itinerary}))
        exit()
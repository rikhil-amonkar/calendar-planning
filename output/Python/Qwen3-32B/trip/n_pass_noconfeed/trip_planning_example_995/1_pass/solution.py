import itertools
import json

required_cities = {
    'Barcelona': 3,
    'Oslo': 2,
    'Stuttgart': 3,
    'Venice': 4,
    'Split': 4,
    'Brussels': 3,
    'Copenhagen': 3
}

direct_flights = [
    ('Venice', 'Stuttgart'),
    ('Oslo', 'Brussels'),
    ('Split', 'Copenhagen'),
    ('Barcelona', 'Copenhagen'),
    ('Barcelona', 'Venice'),
    ('Brussels', 'Venice'),
    ('Barcelona', 'Stuttgart'),
    ('Copenhagen', 'Brussels'),
    ('Oslo', 'Split'),
    ('Oslo', 'Venice'),
    ('Barcelona', 'Split'),
    ('Oslo', 'Copenhagen'),
    ('Barcelona', 'Oslo'),
    ('Copenhagen', 'Stuttgart'),
    ('Split', 'Stuttgart'),
    ('Copenhagen', 'Venice'),
    ('Barcelona', 'Brussels'),
]

direct_flights_set = set()
for a, b in direct_flights:
    direct_flights_set.add((a, b))
    direct_flights_set.add((b, a))

remaining_cities = ['Split', 'Copenhagen', 'Brussels', 'Venice', 'Stuttgart']

for perm in itertools.permutations(remaining_cities):
    # Check transition from Oslo to first city in permutation
    if ('Oslo', perm[0]) not in direct_flights_set:
        continue

    # Check transitions between consecutive cities in permutation
    valid_perm = True
    for i in range(len(perm) - 1):
        if (perm[i], perm[i + 1]) not in direct_flights_set:
            valid_perm = False
            break
    if not valid_perm:
        continue

    # Calculate days for each city in permutation
    previous_end_day = 4  # End of Oslo is day 4
    brussels_start_day = None

    for city in perm:
        duration = required_cities[city]
        start_day = previous_end_day
        if city == 'Brussels':
            brussels_start_day = start_day
        previous_end_day = start_day + duration - 1

    if brussels_start_day == 9:
        # Build the itinerary
        itinerary = []

        # Add Barcelona
        barcelona_days = required_cities['Barcelona']
        barcelona_end = 1 + barcelona_days - 1
        itinerary.append({'day_range': f"Day 1-{barcelona_end + 1}", 'place': 'Barcelona'})

        # Add Oslo
        oslo_days = required_cities['Oslo']
        oslo_start = barcelona_end  # Day 3
        oslo_end = oslo_start + oslo_days - 1  # Day 4
        itinerary.append({'day_range': f"Day {oslo_start}-{oslo_end + 1}", 'place': 'Oslo'})

        # Add remaining cities
        previous_end = oslo_end  # Day 4
        for city in perm:
            duration = required_cities[city]
            start_day = previous_end
            end_day = start_day + duration - 1
            itinerary.append({'day_range': f"Day {start_day}-{end_day + 1}", 'place': city})
            previous_end = end_day

        # Output the JSON
        print(json.dumps({'itinerary': itinerary}))
        exit()
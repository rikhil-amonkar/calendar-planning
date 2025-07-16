import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Lisbon': {'duration': 2, 'constraints': [(4, 5)]},
        'Dubrovnik': {'duration': 5, 'constraints': []},
        'Copenhagen': {'duration': 5, 'constraints': []},
        'Prague': {'duration': 3, 'constraints': []},
        'Tallinn': {'duration': 2, 'constraints': [(1, 2)]},
        'Stockholm': {'duration': 4, 'constraints': [(13, 16)]},
        'Split': {'duration': 3, 'constraints': []},
        'Lyon': {'duration': 2, 'constraints': [(18, 19)]}
    }

    flight_connections = {
        'Dubrovnik': ['Stockholm', 'Copenhagen'],
        'Lisbon': ['Copenhagen', 'Lyon', 'Stockholm', 'Prague'],
        'Copenhagen': ['Lisbon', 'Stockholm', 'Split', 'Dubrovnik', 'Prague', 'Tallinn'],
        'Prague': ['Stockholm', 'Lyon', 'Lisbon', 'Split', 'Copenhagen', 'Tallinn'],
        'Tallinn': ['Stockholm', 'Copenhagen', 'Prague'],
        'Stockholm': ['Dubrovnik', 'Copenhagen', 'Prague', 'Tallinn', 'Lisbon', 'Split'],
        'Split': ['Copenhagen', 'Stockholm', 'Lyon', 'Prague'],
        'Lyon': ['Lisbon', 'Prague', 'Split']
    }

    city_list = list(cities.keys())
    total_days = 19

    for perm in permutations(city_list):
        itinerary = []
        current_day = 1
        valid = True

        for i, city in enumerate(perm):
            duration = cities[city]['duration']
            start_day = current_day
            end_day = current_day + duration - 1

            if i > 0:
                prev_city = perm[i-1]
                if city not in flight_connections[prev_city]:
                    valid = False
                    break

            for (constraint_start, constraint_end) in cities[city]['constraints']:
                if not (constraint_start >= start_day and constraint_end <= end_day):
                    valid = False
                    break

            if not valid:
                break

            itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
            current_day = end_day + 1

            if current_day > total_days:
                valid = False
                break

        if valid and current_day - 1 == total_days:
            # Check all cities are visited
            visited_cities = {item['place'] for item in itinerary}
            if len(visited_cities) == 8:
                return {'itinerary': itinerary}

    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))
import json
from itertools import permutations

def find_valid_itinerary():
    cities = {
        'Dublin': {'duration': 3, 'constraints': [{'type': 'meet', 'start': 7, 'end': 9}]},
        'Madrid': {'duration': 2, 'constraints': [{'type': 'relatives', 'start': 2, 'end': 3}]},
        'Oslo': {'duration': 3, 'constraints': []},
        'London': {'duration': 2, 'constraints': []},
        'Vilnius': {'duration': 3, 'constraints': []},
        'Berlin': {'duration': 5, 'constraints': [{'type': 'wedding', 'start': 3, 'end': 7}]}
    }

    direct_flights = {
        'London': ['Madrid', 'Oslo', 'Dublin', 'Berlin'],
        'Madrid': ['London', 'Oslo', 'Dublin', 'Berlin'],
        'Oslo': ['London', 'Madrid', 'Vilnius', 'Berlin', 'Dublin'],
        'Berlin': ['London', 'Madrid', 'Oslo', 'Vilnius', 'Dublin'],
        'Dublin': ['London', 'Madrid', 'Oslo', 'Berlin'],
        'Vilnius': ['Oslo', 'Berlin']
    }

    city_names = list(cities.keys())
    for perm in permutations(city_names):
        itinerary = []
        current_day = 1
        prev_city = None
        valid = True

        for city in perm:
            if prev_city is not None:
                if city not in direct_flights[prev_city]:
                    valid = False
                    break
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': prev_city,
                    'to': city
                })
                current_day += 1

            duration = cities[city]['duration']
            end_day = current_day + duration - 1
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': city
            })

            for constraint in cities[city]['constraints']:
                if constraint['type'] == 'meet':
                    if not (current_day <= constraint['start'] and end_day >= constraint['end']):
                        valid = False
                        break
                elif constraint['type'] == 'relatives':
                    if not (current_day <= constraint['start'] and end_day >= constraint['end']):
                        valid = False
                        break
                elif constraint['type'] == 'wedding':
                    if not (current_day <= constraint['start'] and end_day >= constraint['end']):
                        valid = False
                        break
            if not valid:
                break

            prev_city = city
            current_day = end_day + 1

        if valid and current_day - 1 <= 13:
            total_days = sum(cities[city]['duration'] for city in perm) + len(perm) - 1
            if total_days <= 13:
                return itinerary

    return None

itinerary = find_valid_itinerary()
if itinerary:
    print(json.dumps(itinerary, indent=2))
else:
    print(json.dumps([{"error": "No valid itinerary found"}], indent=2))
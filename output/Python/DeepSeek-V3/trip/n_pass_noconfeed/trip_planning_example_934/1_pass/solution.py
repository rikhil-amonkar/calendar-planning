import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Brussels': {'duration': 5, 'constraints': [('workshop', 7, 11)]},
        'Rome': {'duration': 2, 'constraints': []},
        'Dubrovnik': {'duration': 3, 'constraints': []},
        'Geneva': {'duration': 5, 'constraints': []},
        'Budapest': {'duration': 2, 'constraints': [('meet_friend', 16, 17)]},
        'Riga': {'duration': 4, 'constraints': [('tour_with_friends', 4, 7)]},
        'Valencia': {'duration': 2, 'constraints': []}
    }

    direct_flights = {
        'Brussels': ['Valencia', 'Geneva', 'Riga', 'Rome', 'Budapest'],
        'Rome': ['Valencia', 'Geneva', 'Riga', 'Budapest', 'Brussels', 'Dubrovnik'],
        'Dubrovnik': ['Geneva', 'Rome'],
        'Geneva': ['Brussels', 'Rome', 'Dubrovnik', 'Valencia', 'Budapest'],
        'Budapest': ['Geneva', 'Rome', 'Brussels'],
        'Riga': ['Rome', 'Brussels'],
        'Valencia': ['Brussels', 'Rome', 'Geneva']
    }

    city_list = list(cities.keys())
    for perm in permutations(city_list):
        itinerary = []
        current_day = 1
        valid = True

        for i, city in enumerate(perm):
            if i > 0:
                prev_city = perm[i-1]
                if city not in direct_flights[prev_city]:
                    valid = False
                    break

            duration = cities[city]['duration']
            day_range = f"Day {current_day}-{current_day + duration - 1}"
            itinerary.append({'day_range': day_range, 'place': city})

            for constraint, start, end in cities[city]['constraints']:
                if not (current_day <= start and current_day + duration - 1 >= end):
                    valid = False
                    break
            if not valid:
                break

            current_day += duration

        if valid and current_day - 1 == 17:
            # Check Riga constraint (4-7)
            riga_found = False
            for entry in itinerary:
                if entry['place'] == 'Riga':
                    start, end = map(int, entry['day_range'].split('Day ')[1].split('-'))
                    if start <= 4 and end >= 7:
                        riga_found = True
                    break
            if not riga_found:
                continue

            # Check Brussels workshop (7-11)
            brussels_found = False
            for entry in itinerary:
                if entry['place'] == 'Brussels':
                    start, end = map(int, entry['day_range'].split('Day ')[1].split('-'))
                    if start <= 7 and end >= 11:
                        brussels_found = True
                    break
            if not brussels_found:
                continue

            # Check Budapest meet friend (16-17)
            budapest_found = False
            for entry in itinerary:
                if entry['place'] == 'Budapest':
                    start, end = map(int, entry['day_range'].split('Day ')[1].split('-'))
                    if start <= 16 and end >= 17:
                        budapest_found = True
                    break
            if not budapest_found:
                continue

            return {'itinerary': itinerary}

    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result))
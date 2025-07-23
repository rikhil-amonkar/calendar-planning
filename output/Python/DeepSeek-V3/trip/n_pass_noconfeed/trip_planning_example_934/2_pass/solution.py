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
            start_day = current_day
            end_day = current_day + duration - 1
            day_range = f"Day {start_day}-{end_day}"
            itinerary.append({'day_range': day_range, 'place': city})

            # Check all constraints for this city
            for constraint, constraint_start, constraint_end in cities[city]['constraints']:
                if not (start_day <= constraint_start and end_day >= constraint_end):
                    valid = False
                    break
            
            if not valid:
                break

            current_day += duration

        if not valid:
            continue

        # Check if total days is exactly 17
        if current_day - 1 != 17:
            continue

        # Verify all special constraints are met
        constraints_met = True
        
        # Check Riga constraint (must include days 4-7)
        riga_ok = False
        for entry in itinerary:
            if entry['place'] == 'Riga':
                start, end = map(int, entry['day_range'].split('Day ')[1].split('-'))
                if start <= 4 and end >= 7:
                    riga_ok = True
                break
        if not riga_ok:
            continue

        # Check Brussels constraint (must include days 7-11)
        brussels_ok = False
        for entry in itinerary:
            if entry['place'] == 'Brussels':
                start, end = map(int, entry['day_range'].split('Day ')[1].split('-'))
                if start <= 7 and end >= 11:
                    brussels_ok = True
                break
        if not brussels_ok:
            continue

        # Check Budapest constraint (must include days 16-17)
        budapest_ok = False
        for entry in itinerary:
            if entry['place'] == 'Budapest':
                start, end = map(int, entry['day_range'].split('Day ')[1].split('-'))
                if start <= 16 and end >= 17:
                    budapest_ok = True
                break
        if not budapest_ok:
            continue

        return {'itinerary': itinerary}

    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))
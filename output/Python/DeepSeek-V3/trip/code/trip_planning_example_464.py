import json
from itertools import permutations

def calculate_itinerary():
    # Input parameters
    total_days = 18
    city_days = {
        'Krakow': 5,
        'Frankfurt': 4,
        'Oslo': 3,
        'Dubrovnik': 5,
        'Naples': 5
    }
    constraints = {
        'Oslo': {'day_range': (16, 18)},
        'Dubrovnik': {'day_range': (5, 9)}
    }
    direct_flights = {
        'Dubrovnik': ['Oslo', 'Frankfurt', 'Naples'],
        'Frankfurt': ['Krakow', 'Oslo', 'Dubrovnik', 'Naples'],
        'Krakow': ['Frankfurt', 'Oslo'],
        'Oslo': ['Dubrovnik', 'Frankfurt', 'Krakow', 'Naples'],
        'Naples': ['Oslo', 'Dubrovnik', 'Frankfurt']
    }

    # Correct typo in direct_flights
    direct_flights['Frankfurt'] = ['Krakow', 'Oslo', 'Dubrovnik', 'Naples']
    direct_flights['Krakow'] = ['Frankfurt', 'Oslo']

    cities = list(city_days.keys())

    # Generate all possible permutations of the cities
    for perm in permutations(cities):
        itinerary = []
        current_day = 1
        valid = True
        prev_city = None

        for city in perm:
            days = city_days[city]
            day_end = current_day + days - 1

            # Check if the city has constraints
            if city in constraints:
                constr_range = constraints[city]['day_range']
                if not (constr_range[0] <= current_day <= constr_range[1] or
                        constr_range[0] <= day_end <= constr_range[1] or
                        (current_day <= constr_range[0] and day_end >= constr_range[1])):
                    valid = False
                    break

            # Check flight connection if not first city
            if prev_city is not None:
                if city not in direct_flights[prev_city]:
                    valid = False
                    break
                itinerary.append({
                    'flying': f'Day {current_day-1}-{current_day-1}',
                    'from': prev_city,
                    'to': city
                })

            itinerary.append({
                'day_range': f'Day {current_day}-{day_end}',
                'place': city
            })
            current_day = day_end + 1
            prev_city = city

        # Check if all days are used and all constraints are met
        if valid and current_day - 1 == total_days:
            return itinerary

    return None

itinerary = calculate_itinerary()
if itinerary:
    print(json.dumps(itinerary, indent=2))
else:
    print(json.dumps({"error": "No valid itinerary found"}, indent=2))
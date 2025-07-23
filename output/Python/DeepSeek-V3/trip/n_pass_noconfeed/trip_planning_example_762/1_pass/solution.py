import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Dublin': {'duration': 3, 'constraints': [(7, 9)]},
        'Madrid': {'duration': 2, 'constraints': [(2, 3)]},
        'Oslo': {'duration': 3, 'constraints': []},
        'London': {'duration': 2, 'constraints': []},
        'Vilnius': {'duration': 3, 'constraints': []},
        'Berlin': {'duration': 5, 'constraints': [(3, 7)]}
    }

    direct_flights = {
        'London': ['Madrid', 'Oslo', 'Dublin', 'Berlin'],
        'Madrid': ['London', 'Oslo', 'Dublin', 'Berlin'],
        'Oslo': ['Vilnius', 'Madrid', 'London', 'Berlin', 'Dublin'],
        'Berlin': ['Vilnius', 'Madrid', 'Oslo', 'London', 'Dublin'],
        'Dublin': ['Madrid', 'Oslo', 'London', 'Berlin'],
        'Vilnius': ['Oslo', 'Berlin']
    }

    city_list = list(cities.keys())
    for perm in permutations(city_list):
        itinerary = []
        current_city = None
        remaining_days = {city: cities[city]['duration'] for city in cities}
        constraints_met = {city: False for city in cities if cities[city]['constraints']}
        day = 1

        for city in perm:
            if current_city is None:
                current_city = city
                start_day = day
                end_day = start_day + cities[city]['duration'] - 1
                if remaining_days[city] > 0:
                    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
                    day = end_day + 1
                    remaining_days[city] = 0
                    # Check constraints
                    if cities[city]['constraints']:
                        for (start, end) in cities[city]['constraints']:
                            if start_day <= start and end_day >= end:
                                constraints_met[city] = True
            else:
                if city in direct_flights[current_city]:
                    transition_day = day
                    # Spend remaining days in current city before moving
                    if remaining_days[current_city] > 0:
                        start_day = day
                        end_day = start_day + remaining_days[current_city] - 1
                        itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': current_city})
                        day = end_day + 1
                        remaining_days[current_city] = 0
                        # Check constraints
                        if cities[current_city]['constraints']:
                            for (start, end) in cities[current_city]['constraints']:
                                if start_day <= start and end_day >= end:
                                    constraints_met[current_city] = True
                    # Move to next city
                    start_day = day
                    end_day = start_day + cities[city]['duration'] - 1
                    if remaining_days[city] > 0:
                        itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
                        day = end_day + 1
                        remaining_days[city] = 0
                        # Check constraints
                        if cities[city]['constraints']:
                            for (start, end) in cities[city]['constraints']:
                                if start_day <= start and end_day >= end:
                                    constraints_met[city] = True
                    current_city = city
                else:
                    break

        # Check if all cities are visited and constraints are met
        if all(v == 0 for v in remaining_days.values()) and all(constraints_met.values()):
            if day - 1 <= 13:
                return {'itinerary': itinerary}

    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result))
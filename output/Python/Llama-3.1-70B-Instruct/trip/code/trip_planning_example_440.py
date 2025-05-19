import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    cities = list(constraints.keys())
    unvisited_cities = cities.copy()
    current_city = None

    # Start with Split
    current_city = 'Split'
    unvisited_cities.remove(current_city)
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[current_city] - 1}', 'place': current_city})
    current_day += constraints[current_city]

    # Visit Helsinki
    next_city = 'Helsinki'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Vilnius
    next_city = 'Vilnius'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    if current_day < 7:
        trip_plan.append({'day_range': f'Day {current_day}-{6}', 'place': next_city})
        current_day = 7
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': next_city})
    current_city = next_city
    current_day += 3

    # Visit Geneva
    next_city = 'Geneva'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Reykjavik
    next_city = 'Reykjavik'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    if current_day < 10:
        trip_plan.append({'day_range': f'Day {current_day}-{9}', 'place': next_city})
        current_day = 10
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': next_city})

    return trip_plan

constraints = {
    'Split': 2,
    'Helsinki': 2,
    'Reykjavik': 3,
    'Vilnius': 3,
    'Geneva': 6
}

direct_flights = [
    ['Split', 'Helsinki'],
    ['Geneva', 'Split'],
    ['Geneva', 'Helsinki'],
    ['Helsinki', 'Reykjavik'],
    ['Vilnius', 'Helsinki'],
    ['Split', 'Vilnius']
]

trip_plan = calculate_trip_plan(constraints, direct_flights)
print(json.dumps(trip_plan, indent=4))
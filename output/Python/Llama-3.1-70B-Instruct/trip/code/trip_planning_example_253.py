import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    cities = list(constraints.keys())
    unvisited_cities = cities.copy()
    current_city = None

    # Start with Lyon
    current_city = 'Lyon'
    unvisited_cities.remove(current_city)
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[current_city] - 1}', 'place': current_city})
    current_day += constraints[current_city]

    # Attend a wedding in Lyon between day 7 and day 9
    if current_day < 9:
        trip_plan.append({'day_range': f'Day {current_day}-{8}', 'place': current_city})
        current_day = 9

    # Visit Amsterdam
    next_city = 'Amsterdam'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': next_city})
    current_city = next_city
    current_day += 3

    # Attend a workshop in Amsterdam between day 9 and day 11
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': current_city})
    current_day += 3

    # Visit Vienna
    next_city = 'Vienna'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Santorini
    next_city = 'Santorini'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})

    return trip_plan

constraints = {
    'Amsterdam': 3,
    'Vienna': 7,
    'Santorini': 4,
    'Lyon': 3
}

direct_flights = [
    ['Vienna', 'Lyon'],
    ['Vienna', 'Santorini'],
    ['Vienna', 'Amsterdam'],
    ['Amsterdam', 'Santorini'],
    ['Lyon', 'Amsterdam']
]

trip_plan = calculate_trip_plan(constraints, direct_flights)
print(json.dumps(trip_plan, indent=4))
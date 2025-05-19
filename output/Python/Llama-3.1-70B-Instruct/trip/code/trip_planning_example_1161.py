import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    cities = list(constraints.keys())
    unvisited_cities = cities.copy()
    current_city = None

    # Start with Oslo
    current_city = 'Oslo'
    unvisited_cities.remove(current_city)
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[current_city] - 1}', 'place': current_city})
    current_day += constraints[current_city]

    # Meet friends in Oslo between day 1 and day 2
    if current_day < 2:
        trip_plan.append({'day_range': f'Day {current_day}-{1}', 'place': current_city})
        current_day = 2

    # Visit Helsinki
    next_city = 'Helsinki'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Dubrovnik
    next_city = 'Dubrovnik'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 3}', 'place': next_city})
    current_city = next_city
    current_day += 4

    # Attend an annual show in Dubrovnik from day 2 to day 4
    if current_day < 4:
        trip_plan.append({'day_range': f'Day {current_day}-{3}', 'place': current_city})
        current_day = 4

    # Visit Vilnius
    next_city = 'Vilnius'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Krakow
    next_city = 'Krakow'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Paris
    next_city = 'Paris'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Madrid
    next_city = 'Madrid'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Mykonos
    next_city = 'Mykonos'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    if current_day < 15:
        trip_plan.append({'day_range': f'Day {current_day}-{14}', 'place': next_city})
        current_day = 15
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 3}', 'place': next_city})

    return trip_plan

constraints = {
    'Mykonos': 4,
    'Krakow': 5,
    'Vilnius': 2,
    'Helsinki': 2,
    'Dubrovnik': 3,
    'Oslo': 2,
    'Madrid': 5,
    'Paris': 2
}

direct_flights = [
    ['Oslo', 'Krakow'],
    ['Oslo', 'Paris'],
    ['Paris', 'Madrid'],
    ['Helsinki', 'Vilnius'],
    ['Oslo', 'Madrid'],
    ['Oslo', 'Helsinki'],
    ['Helsinki', 'Krakow'],
    ['Dubrovnik', 'Helsinki'],
    ['Dubrovnik', 'Madrid'],
    ['Oslo', 'Dubrovnik'],
    ['Krakow', 'Paris'],
    ['Madrid', 'Mykonos'],
    ['Oslo', 'Vilnius'],
    ['Krakow', 'Vilnius'],
    ['Helsinki', 'Paris'],
    ['Vilnius', 'Paris'],
    ['Helsinki', 'Madrid']
]

trip_plan = calculate_trip_plan(constraints, direct_flights)
print(json.dumps(trip_plan, indent=4))
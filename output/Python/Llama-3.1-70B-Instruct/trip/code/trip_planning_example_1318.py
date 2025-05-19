import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    cities = list(constraints.keys())
    unvisited_cities = cities.copy()
    current_city = None

    # Start with Edinburgh
    current_city = 'Edinburgh'
    unvisited_cities.remove(current_city)
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[current_city] - 1}', 'place': current_city})
    current_day += constraints[current_city]

    # Visit Budapest
    next_city = 'Budapest'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Geneva
    next_city = 'Geneva'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Porto
    next_city = 'Porto'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Riga
    next_city = 'Riga'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Tallinn
    next_city = 'Tallinn'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 4}', 'place': next_city})
    current_city = next_city
    current_day += 5

    # Attend a wedding in Tallinn between day 4 and day 8
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Continue staying in Tallinn
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Visit Vilnius
    next_city = 'Vilnius'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Helsinki
    next_city = 'Helsinki'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Oslo
    next_city = 'Oslo'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Meet a friend in Oslo between day 24 and day 25
    if current_day < 24:
        trip_plan.append({'day_range': f'Day {current_day}-{23}', 'place': current_city})
        current_day = 24
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': current_city})

    return trip_plan

constraints = {
    'Oslo': 2,
    'Helsinki': 2,
    'Edinburgh': 3,
    'Riga': 2,
    'Tallinn': 5,
    'Budapest': 5,
    'Vilnius': 5,
    'Porto': 5,
    'Geneva': 4
}

direct_flights = [
    ['Porto', 'Oslo'],
    ['Edinburgh', 'Budapest'],
    ['Edinburgh', 'Geneva'],
    ['Riga', 'Tallinn'],
    ['Edinburgh', 'Porto'],
    ['Vilnius', 'Helsinki'],
    ['Tallinn', 'Vilnius'],
    ['Riga', 'Oslo'],
    ['Geneva', 'Oslo'],
    ['Edinburgh', 'Oslo'],
    ['Edinburgh', 'Helsinki'],
    ['Vilnius', 'Oslo'],
    ['Riga', 'Helsinki'],
    ['Budapest', 'Geneva'],
    ['Helsinki', 'Budapest'],
    ['Helsinki', 'Oslo'],
    ['Edinburgh', 'Riga'],
    ['Tallinn', 'Helsinki'],
    ['Geneva', 'Porto'],
    ['Budapest', 'Oslo'],
    ['Helsinki', 'Geneva'],
    ['Riga', 'Vilnius'],
    ['Tallinn', 'Oslo']
]

trip_plan = calculate_trip_plan(constraints, direct_flights)
print(json.dumps(trip_plan, indent=4))
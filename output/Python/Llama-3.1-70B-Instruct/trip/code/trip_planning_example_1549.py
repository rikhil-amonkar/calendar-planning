import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    cities = list(constraints.keys())
    unvisited_cities = cities.copy()
    current_city = None

    # Start with Riga
    current_city = 'Riga'
    unvisited_cities.remove(current_city)
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 4}', 'place': current_city})
    current_day += 5

    # Attend an annual show in Riga between day 5 and day 8
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Continue staying in Riga
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Visit Prague
    next_city = 'Prague'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Tallinn
    next_city = 'Tallinn'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': next_city})
    current_city = next_city
    current_day += 3

    # Visit Warsaw
    next_city = 'Warsaw'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Naples
    next_city = 'Naples'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Milan
    next_city = 'Milan'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': next_city})
    current_city = next_city
    current_day += 3

    # Meet a friend in Milan between day 24 and day 26
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Continue staying in Milan
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Visit Porto
    next_city = 'Porto'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Lisbon
    next_city = 'Lisbon'
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
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Stockholm
    next_city = 'Stockholm'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})

    return trip_plan

constraints = {
    'Prague': 5,
    'Tallinn': 3,
    'Warsaw': 2,
    'Porto': 3,
    'Naples': 5,
    'Milan': 3,
    'Lisbon': 5,
    'Santorini': 5,
    'Riga': 4,
    'Stockholm': 2
}

direct_flights = [
    ['Riga', 'Prague'],
    ['Stockholm', 'Milan'],
    ['Riga', 'Milan'],
    ['Lisbon', 'Stockholm'],
    ['Stockholm', 'Santorini'],
    ['Naples', 'Warsaw'],
    ['Lisbon', 'Warsaw'],
    ['Naples', 'Milan'],
    ['Lisbon', 'Naples'],
    ['Riga', 'Tallinn'],
    ['Tallinn', 'Prague'],
    ['Stockholm', 'Warsaw'],
    ['Riga', 'Warsaw'],
    ['Lisbon', 'Riga'],
    ['Riga', 'Stockholm'],
    ['Lisbon', 'Porto'],
    ['Lisbon', 'Prague'],
    ['Milan', 'Porto'],
    ['Prague', 'Milan'],
    ['Lisbon', 'Milan'],
    ['Warsaw', 'Porto'],
    ['Warsaw', 'Tallinn'],
    ['Santorini', 'Milan'],
    ['Stockholm', 'Prague'],
    ['Stockholm', 'Tallinn'],
    ['Warsaw', 'Milan'],
    ['Santorini', 'Naples'],
    ['Warsaw', 'Prague']
]

trip_plan = calculate_trip_plan(constraints, direct_flights)
print(json.dumps(trip_plan, indent=4))
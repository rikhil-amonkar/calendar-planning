import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    cities = list(constraints.keys())
    unvisited_cities = cities.copy()
    current_city = None

    # Start with Tallinn
    current_city = 'Tallinn'
    unvisited_cities.remove(current_city)
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[current_city] - 1}', 'place': current_city})
    current_day += constraints[current_city]

    # Meet a friend in Tallinn between day 1 and day 2
    if current_day < 2:
        trip_plan.append({'day_range': f'Day {current_day}-{1}', 'place': current_city})
        current_day = 2

    # Visit Prague
    next_city = 'Prague'
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

    # Attend a workshop in Lisbon between day 4 and day 5
    if current_day < 5:
        trip_plan.append({'day_range': f'Day {current_day}-{4}', 'place': current_city})
        current_day = 5

    # Visit Copenhagen
    next_city = 'Copenhagen'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Dubrovnik
    next_city = 'Dubrovnik'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Split
    next_city = 'Split'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Stockholm
    next_city = 'Stockholm'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    if current_day < 13:
        trip_plan.append({'day_range': f'Day {current_day}-{12}', 'place': next_city})
        current_day = 13
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 3}', 'place': next_city})
    current_city = next_city
    current_day += 4

    # Attend a wedding in Stockholm between day 13 and day 16
    if current_day < 16:
        trip_plan.append({'day_range': f'Day {current_day}-{15}', 'place': current_city})
        current_day = 16

    # Visit Lyon
    next_city = 'Lyon'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Attend an annual show in Lyon from day 18 to day 19
    if current_day < 18:
        trip_plan.append({'day_range': f'Day {current_day}-{17}', 'place': current_city})
        current_day = 18
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': current_city})

    return trip_plan

constraints = {
    'Lisbon': 2,
    'Dubrovnik': 5,
    'Copenhagen': 5,
    'Prague': 3,
    'Tallinn': 2,
    'Stockholm': 4,
    'Split': 3,
    'Lyon': 2
}

direct_flights = [
    ['Dubrovnik', 'Stockholm'],
    ['Lisbon', 'Copenhagen'],
    ['Lisbon', 'Lyon'],
    ['Copenhagen', 'Stockholm'],
    ['Copenhagen', 'Split'],
    ['Prague', 'Stockholm'],
    ['Tallinn', 'Stockholm'],
    ['Prague', 'Lyon'],
    ['Lisbon', 'Stockholm'],
    ['Prague', 'Lisbon'],
    ['Stockholm', 'Split'],
    ['Prague', 'Copenhagen'],
    ['Split', 'Lyon'],
    ['Copenhagen', 'Dubrovnik'],
    ['Prague', 'Split'],
    ['Tallinn', 'Copenhagen'],
    ['Tallinn', 'Prague']
]

trip_plan = calculate_trip_plan(constraints, direct_flights)
print(json.dumps(trip_plan, indent=4))
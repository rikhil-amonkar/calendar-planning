import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    cities = list(constraints.keys())
    unvisited_cities = cities.copy()
    current_city = None

    # Start with Vienna
    current_city = 'Vienna'
    unvisited_cities.remove(current_city)
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 3}', 'place': current_city})
    current_day += 4

    # Attend a conference in Vienna between day 1 and day 4
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Visit Milan
    next_city = 'Milan'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Rome
    next_city = 'Rome'
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

    # Visit Vilnius
    next_city = 'Vilnius'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Lisbon
    next_city = 'Lisbon'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    if current_day < 11:
        trip_plan.append({'day_range': f'Day {current_day}-{10}', 'place': next_city})
        current_day = 11
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': next_city})
    current_city = next_city
    current_day += 3

    # Visit Oslo
    next_city = 'Oslo'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    if current_day < 13:
        trip_plan.append({'day_range': f'Day {current_day}-{12}', 'place': next_city})
        current_day = 13
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': next_city})

    return trip_plan

constraints = {
    'Vienna': 4,
    'Milan': 2,
    'Rome': 3,
    'Riga': 2,
    'Lisbon': 3,
    'Vilnius': 4,
    'Oslo': 3
}

direct_flights = [
    ['Riga', 'Oslo'],
    ['Rome', 'Oslo'],
    ['Vienna', 'Milan'],
    ['Vienna', 'Vilnius'],
    ['Vienna', 'Lisbon'],
    ['Riga', 'Milan'],
    ['Lisbon', 'Oslo'],
    ['Rome', 'Riga'],
    ['Rome', 'Lisbon'],
    ['Vienna', 'Riga'],
    ['Vienna', 'Rome'],
    ['Milan', 'Oslo'],
    ['Vienna', 'Oslo'],
    ['Vilnius', 'Oslo'],
    ['Riga', 'Vilnius'],
    ['Vilnius', 'Milan'],
    ['Riga', 'Lisbon'],
    ['Milan', 'Lisbon']
]

trip_plan = calculate_trip_plan(constraints, direct_flights)
print(json.dumps(trip_plan, indent=4))
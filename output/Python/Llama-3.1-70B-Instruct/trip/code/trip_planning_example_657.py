import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    cities = list(constraints.keys())
    unvisited_cities = cities.copy()
    current_city = None

    # Start with Valencia
    current_city = 'Valencia'
    unvisited_cities.remove(current_city)
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[current_city] - 1}', 'place': current_city})
    current_day += constraints[current_city]

    # Visit Naples
    next_city = 'Naples'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Manchester
    next_city = 'Manchester'
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

    # Visit Vilnius
    next_city = 'Vilnius'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    if current_day < 12:
        trip_plan.append({'day_range': f'Day {current_day}-{11}', 'place': next_city})
        current_day = 12
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': next_city})
    current_city = next_city
    current_day += 2

    # Attend a wedding in Vilnius between day 12 and day 13
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Visit Frankfurt
    next_city = 'Frankfurt'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    if current_day < 13:
        trip_plan.append({'day_range': f'Day {current_day}-{12}', 'place': next_city})
        current_day = 13
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 3}', 'place': next_city})

    return trip_plan

constraints = {
    'Frankfurt': 4,
    'Manchester': 4,
    'Valencia': 4,
    'Naples': 4,
    'Oslo': 3,
    'Vilnius': 2
}

direct_flights = [
    ['Valencia', 'Frankfurt'],
    ['Manchester', 'Frankfurt'],
    ['Naples', 'Manchester'],
    ['Naples', 'Frankfurt'],
    ['Naples', 'Oslo'],
    ['Oslo', 'Frankfurt'],
    ['Vilnius', 'Frankfurt'],
    ['Oslo', 'Vilnius'],
    ['Manchester', 'Oslo'],
    ['Valencia', 'Naples']
]

trip_plan = calculate_trip_plan(constraints, direct_flights)
print(json.dumps(trip_plan, indent=4))
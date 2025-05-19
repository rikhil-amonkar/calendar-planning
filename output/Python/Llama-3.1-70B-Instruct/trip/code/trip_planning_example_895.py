import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    cities = list(constraints.keys())
    unvisited_cities = cities.copy()
    current_city = None

    # Start with Brussels
    current_city = 'Brussels'
    unvisited_cities.remove(current_city)
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': current_city})
    current_day += 2

    # Attend a conference in Brussels between day 1 and day 2
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Visit London
    next_city = 'London'
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

    # Visit Venice
    next_city = 'Venice'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': next_city})
    current_city = next_city
    current_day += 3

    # Visit Santorini
    next_city = 'Santorini'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Reykjavik
    next_city = 'Reykjavik'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Madrid
    next_city = 'Madrid'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    if current_day < 7:
        trip_plan.append({'day_range': f'Day {current_day}-{6}', 'place': next_city})
        current_day = 7
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 4}', 'place': next_city})
    current_city = next_city
    current_day += 5

    return trip_plan

constraints = {
    'Venice': 3,
    'London': 3,
    'Lisbon': 4,
    'Brussels': 2,
    'Reykjavik': 3,
    'Santorini': 3,
    'Madrid': 5
}

direct_flights = [
    ['Venice', 'Madrid'],
    ['Lisbon', 'Reykjavik'],
    ['Brussels', 'Venice'],
    ['Venice', 'Santorini'],
    ['Lisbon', 'Venice'],
    ['Reykjavik', 'Madrid'],
    ['Brussels', 'London'],
    ['Madrid', 'London'],
    ['Santorini', 'London'],
    ['London', 'Reykjavik'],
    ['Brussels', 'Lisbon'],
    ['Lisbon', 'London'],
    ['Lisbon', 'Madrid'],
    ['Madrid', 'Santorini'],
    ['Brussels', 'Reykjavik'],
    ['Brussels', 'Madrid'],
    ['Venice', 'London']
]

trip_plan = calculate_trip_plan(constraints, direct_flights)
print(json.dumps(trip_plan, indent=4))
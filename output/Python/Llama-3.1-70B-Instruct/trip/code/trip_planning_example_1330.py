import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    cities = list(constraints.keys())
    unvisited_cities = cities.copy()
    current_city = None

    # Start with Salzburg
    current_city = 'Salzburg'
    unvisited_cities.remove(current_city)
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[current_city] - 1}', 'place': current_city})
    current_day += constraints[current_city]

    # Visit Hamburg
    next_city = 'Hamburg'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Nice
    next_city = 'Nice'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': next_city})
    current_city = next_city
    current_day += 3

    # Visit Zurich
    next_city = 'Zurich'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Brussels
    next_city = 'Brussels'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Bucharest
    next_city = 'Bucharest'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Venice
    next_city = 'Venice'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Copenhagen
    next_city = 'Copenhagen'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    if current_day < 18:
        trip_plan.append({'day_range': f'Day {current_day}-{17}', 'place': next_city})
        current_day = 18
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 3}', 'place': next_city})
    current_city = next_city
    current_day += 4

    # Attend a wedding in Copenhagen between day 18 and day 21
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Continue staying in Copenhagen
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Visit Naples
    next_city = 'Naples'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    if current_day < 22:
        trip_plan.append({'day_range': f'Day {current_day}-{21}', 'place': next_city})
        current_day = 22
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 3}', 'place': next_city})

    return trip_plan

constraints = {
    'Salzburg': 2,
    'Venice': 5,
    'Bucharest': 4,
    'Brussels': 2,
    'Hamburg': 4,
    'Copenhagen': 4,
    'Nice': 3,
    'Zurich': 5,
    'Naples': 4
}

direct_flights = [
    ['Zurich', 'Brussels'],
    ['Bucharest', 'Copenhagen'],
    ['Venice', 'Brussels'],
    ['Nice', 'Zurich'],
    ['Hamburg', 'Nice'],
    ['Zurich', 'Naples'],
    ['Hamburg', 'Bucharest'],
    ['Zurich', 'Copenhagen'],
    ['Bucharest', 'Brussels'],
    ['Hamburg', 'Brussels'],
    ['Venice', 'Naples'],
    ['Venice', 'Copenhagen'],
    ['Bucharest', 'Naples'],
    ['Hamburg', 'Copenhagen'],
    ['Venice', 'Zurich'],
    ['Nice', 'Brussels'],
    ['Hamburg', 'Venice'],
    ['Copenhagen', 'Naples'],
    ['Nice', 'Naples'],
    ['Hamburg', 'Zurich'],
    ['Salzburg', 'Hamburg'],
    ['Zurich', 'Bucharest'],
    ['Brussels', 'Naples'],
    ['Copenhagen', 'Brussels'],
    ['Venice', 'Nice'],
    ['Nice', 'Copenhagen']
]

trip_plan = calculate_trip_plan(constraints, direct_flights)
print(json.dumps(trip_plan, indent=4))
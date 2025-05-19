import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    cities = list(constraints.keys())
    unvisited_cities = cities.copy()
    current_city = None

    # Start with Reykjavik
    current_city = 'Reykjavik'
    unvisited_cities.remove(current_city)
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[current_city] - 1}', 'place': current_city})
    current_day += constraints[current_city]

    # Meet a friend in Reykjavik between day 3 and day 4
    if current_day < 4:
        trip_plan.append({'day_range': f'Day {current_day}-{3}', 'place': current_city})
        current_day = 4

    # Visit Stockholm
    next_city = 'Stockholm'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Meet friends at Stockholm between day 4 and day 5 to tour together
    if current_day < 5:
        trip_plan.append({'day_range': f'Day {current_day}-{4}', 'place': current_city})
        current_day = 5

    # Visit Nice
    next_city = 'Nice'
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

    # Visit Vienna and attend a workshop
    next_city = 'Vienna'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    if current_day < 11:
        trip_plan.append({'day_range': f'Day {current_day}-{10}', 'place': current_city})
        current_day = 11
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': current_city})
    current_day += 3

    # Visit Split
    next_city = 'Split'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Copenhagen
    next_city = 'Copenhagen'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Porto and attend a wedding
    next_city = 'Porto'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    if current_day < 13:
        trip_plan.append({'day_range': f'Day {current_day}-{12}', 'place': next_city})
        current_day = 13
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})

    return trip_plan

constraints = {
    'Reykjavik': 2,
    'Stockholm': 2,
    'Porto': 5,
    'Nice': 3,
    'Venice': 4,
    'Vienna': 3,
    'Split': 3,
    'Copenhagen': 2
}

direct_flights = [
    ['Copenhagen', 'Vienna'],
    ['Nice', 'Stockholm'],
    ['Split', 'Copenhagen'],
    ['Nice', 'Reykjavik'],
    ['Nice', 'Porto'],
    ['Reykjavik', 'Vienna'],
    ['Stockholm', 'Copenhagen'],
    ['Nice', 'Venice'],
    ['Nice', 'Vienna'],
    ['Reykjavik', 'Copenhagen'],
    ['Nice', 'Copenhagen'],
    ['Stockholm', 'Vienna'],
    ['Venice', 'Vienna'],
    ['Copenhagen', 'Porto'],
    ['Reykjavik', 'Stockholm'],
    ['Stockholm', 'Split'],
    ['Split', 'Vienna'],
    ['Copenhagen', 'Venice'],
    ['Vienna', 'Porto']
]

trip_plan = calculate_trip_plan(constraints, direct_flights)
print(json.dumps(trip_plan, indent=4))
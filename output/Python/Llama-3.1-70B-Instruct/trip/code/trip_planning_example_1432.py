import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    cities = list(constraints.keys())
    unvisited_cities = cities.copy()
    current_city = None

    # Start with Stockholm
    current_city = 'Stockholm'
    unvisited_cities.remove(current_city)
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[current_city] - 1}', 'place': current_city})
    current_day += constraints[current_city]

    # Meet a friend in Stockholm between day 1 and day 3
    if current_day < 3:
        trip_plan.append({'day_range': f'Day {current_day}-{2}', 'place': current_city})
        current_day = 3

    # Visit Vienna
    next_city = 'Vienna'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 4}', 'place': next_city})
    current_city = next_city
    current_day += 5

    # Attend a wedding in Vienna between day 6 and day 10
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Continue staying in Vienna
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Visit Valencia
    next_city = 'Valencia'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': next_city})
    current_city = next_city
    current_day += 2

    # Attend an annual show in Valencia between day 5 and day 6
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Continue staying in Valencia
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Visit Frankfurt
    next_city = 'Frankfurt'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Salzburg
    next_city = 'Salzburg'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Athens
    next_city = 'Athens'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 4}', 'place': next_city})
    current_city = next_city
    current_day += 5

    # Attend a workshop in Athens between day 14 and day 18
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Continue staying in Athens
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Visit Riga
    next_city = 'Riga'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': next_city})
    current_city = next_city
    current_day += 3

    # Attend a conference in Riga between day 18 and day 20
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': current_city})
    current_day += 3

    # Visit Bucharest
    next_city = 'Bucharest'
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

    # Visit Amsterdam
    next_city = 'Amsterdam'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})

    return trip_plan

constraints = {
    'Frankfurt': 4,
    'Salzburg': 5,
    'Athens': 5,
    'Reykjavik': 5,
    'Bucharest': 3,
    'Valencia': 2,
    'Vienna': 5,
    'Amsterdam': 3,
    'Stockholm': 3,
    'Riga': 3
}

direct_flights = [
    ['Valencia', 'Frankfurt'],
    ['Vienna', 'Bucharest'],
    ['Valencia', 'Athens'],
    ['Athens', 'Bucharest'],
    ['Riga', 'Frankfurt'],
    ['Stockholm', 'Athens'],
    ['Amsterdam', 'Bucharest'],
    ['Athens', 'Riga'],
    ['Amsterdam', 'Frankfurt'],
    ['Stockholm', 'Vienna'],
    ['Vienna', 'Riga'],
    ['Amsterdam', 'Reykjavik'],
    ['Reykjavik', 'Frankfurt'],
    ['Stockholm', 'Amsterdam'],
    ['Amsterdam', 'Valencia'],
    ['Vienna', 'Frankfurt'],
    ['Valencia', 'Bucharest'],
    ['Bucharest', 'Frankfurt'],
    ['Stockholm', 'Frankfurt'],
    ['Valencia', 'Vienna'],
    ['Reykjavik', 'Athens'],
    ['Frankfurt', 'Salzburg'],
    ['Amsterdam', 'Vienna'],
    ['Stockholm', 'Reykjavik'],
    ['Amsterdam', 'Riga'],
    ['Stockholm', 'Riga'],
    ['Vienna', 'Reykjavik'],
    ['Amsterdam', 'Athens'],
    ['Athens', 'Frankfurt'],
    ['Vienna', 'Athens'],
    ['Riga', 'Bucharest']
]

trip_plan = calculate_trip_plan(constraints, direct_flights)
print(json.dumps(trip_plan, indent=4))
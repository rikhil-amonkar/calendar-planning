import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    cities = list(constraints.keys())
    unvisited_cities = cities.copy()
    current_city = None

    # Start with Hamburg
    current_city = 'Hamburg'
    unvisited_cities.remove(current_city)
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': current_city})
    current_day += 2

    # Meet friends in Hamburg between day 1 and day 2
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Visit Dublin
    next_city = 'Dublin'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    if current_day < 2:
        trip_plan.append({'day_range': f'Day {current_day}-{1}', 'place': next_city})
        current_day = 2
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 4}', 'place': next_city})
    current_city = next_city
    current_day += 5

    # Attend an annual show in Dublin between day 2 and day 6
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Continue staying in Dublin
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Visit Helsinki
    next_city = 'Helsinki'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Reykjavik
    next_city = 'Reykjavik'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': next_city})
    current_city = next_city
    current_day += 2

    # Attend a wedding in Reykjavik between day 9 and day 10
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Continue staying in Reykjavik
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Visit London
    next_city = 'London'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Mykonos
    next_city = 'Mykonos'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})

    return trip_plan

constraints = {
    'Mykonos': 3,
    'Reykjavik': 2,
    'Dublin': 5,
    'London': 5,
    'Helsinki': 4,
    'Hamburg': 2
}

direct_flights = [
    ['Dublin', 'London'],
    ['Hamburg', 'Dublin'],
    ['Helsinki', 'Reykjavik'],
    ['Hamburg', 'London'],
    ['Dublin', 'Helsinki'],
    ['Reykjavik', 'London'],
    ['London', 'Mykonos'],
    ['Dublin', 'Reykjavik'],
    ['Hamburg', 'Helsinki'],
    ['Helsinki', 'London']
]

trip_plan = calculate_trip_plan(constraints, direct_flights)
print(json.dumps(trip_plan, indent=4))
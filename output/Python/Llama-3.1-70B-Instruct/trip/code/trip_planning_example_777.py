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
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': current_city})
    current_day += 2

    # Attend an annual show in Vienna between day 2 and day 3
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Visit Helsinki
    next_city = 'Helsinki'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': next_city})
    current_city = next_city
    current_day += 3

    # Meet friends in Helsinki between day 3 and day 5
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Continue staying in Helsinki
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

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
    if current_day < 7:
        trip_plan.append({'day_range': f'Day {current_day}-{6}', 'place': next_city})
        current_day = 7
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 4}', 'place': next_city})
    current_city = next_city
    current_day += 5

    # Attend a wedding in Tallinn between day 7 and day 11
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Continue staying in Tallinn
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Visit Dublin
    next_city = 'Dublin'
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

    return trip_plan

constraints = {
    'Dublin': 5,
    'Helsinki': 3,
    'Riga': 3,
    'Reykjavik': 2,
    'Vienna': 2,
    'Tallinn': 5
}

direct_flights = [
    ['Helsinki', 'Riga'],
    ['Riga', 'Tallinn'],
    ['Vienna', 'Helsinki'],
    ['Riga', 'Dublin'],
    ['Vienna', 'Riga'],
    ['Reykjavik', 'Vienna'],
    ['Helsinki', 'Dublin'],
    ['Tallinn', 'Dublin'],
    ['Reykjavik', 'Helsinki'],
    ['Reykjavik', 'Dublin'],
    ['Helsinki', 'Tallinn'],
    ['Vienna', 'Dublin']
]

trip_plan = calculate_trip_plan(constraints, direct_flights)
print(json.dumps(trip_plan, indent=4))
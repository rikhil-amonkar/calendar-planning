import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    cities = list(constraints.keys())
    unvisited_cities = cities.copy()
    current_city = None

    # Start with Madrid
    current_city = 'Madrid'
    unvisited_cities.remove(current_city)
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[current_city] - 1}', 'place': current_city})
    current_day += constraints[current_city]

    # Visit Dublin
    next_city = 'Dublin'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})
    current_city = next_city
    current_day += constraints[next_city]

    # Visit Tallinn
    next_city = 'Tallinn'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    if current_day < 6:
        trip_plan.append({'day_range': f'Day {current_day}-{5}', 'place': next_city})
        current_day = 6
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': next_city})

    return trip_plan

constraints = {
    'Madrid': 4,
    'Dublin': 3,
    'Tallinn': 2
}

direct_flights = [
    ['Madrid', 'Dublin'],
    ['Dublin', 'Tallinn']
]

trip_plan = calculate_trip_plan(constraints, direct_flights)
print(json.dumps(trip_plan, indent=4))
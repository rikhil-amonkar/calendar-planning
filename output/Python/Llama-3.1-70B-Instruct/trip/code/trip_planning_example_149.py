import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    cities = list(constraints.keys())
    unvisited_cities = cities.copy()
    current_city = None

    # Start with London
    current_city = 'London'
    unvisited_cities.remove(current_city)
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[current_city] - 1}', 'place': current_city})
    current_day += constraints[current_city]

    # Visit Santorini
    next_city = 'Santorini'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 4}', 'place': next_city})
    current_city = next_city
    current_day += 5

    # Attend a conference in Santorini on day 5
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Continue staying in Santorini
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + 4}', 'place': current_city})
    current_day += 5

    # Attend a conference in Santorini on day 10
    trip_plan.append({'day_range': f'Day {current_day}-{current_day}', 'place': current_city})
    current_day += 1

    # Visit Istanbul
    next_city = 'Istanbul'
    unvisited_cities.remove(next_city)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': next_city})
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + constraints[next_city] - 1}', 'place': next_city})

    return trip_plan

constraints = {
    'London': 3,
    'Santorini': 6,
    'Istanbul': 3
}

direct_flights = [
    ['Istanbul', 'London'],
    ['London', 'Santorini']
]

trip_plan = calculate_trip_plan(constraints, direct_flights)
print(json.dumps(trip_plan, indent=4))
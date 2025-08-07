from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Frankfurt', 'Naples', 'Helsinki', 'Lyon', 'Prague']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_days = 12

    # Direct flights: adjacency list
    adjacency = {
        'Prague': ['Lyon', 'Frankfurt', 'Helsinki'],
        'Lyon': ['Prague', 'Frankfurt'],
        'Frankfurt': ['Prague', 'Lyon', 'Helsinki', 'Naples'],
        'Helsinki': ['Prague', 'Frankfurt', 'Naples'],
        'Naples': ['Helsinki', 'Frankfurt']
    }

    # Create Z3 variables: each day is assigned a city (index)
    day_to_city = [Int(f'day_{i}_city') for i in range(1, n_days + 1)]

    solver = Solver()

    # Each day's city must be a valid city index (0 to 4)
    for day in day_to_city:
        solver.add(day >= 0, day < 5)

    # Flight transitions: consecutive days must be same city or connected by a direct flight
    for i in range(n_days - 1):
        current_city = day_to_city[i]
        next_city = day_to_city[i + 1]
        # Either stay in the same city or move to a connected city
        same_city = current_city == next_city
        # Or, if different, must be adjacent
        possible_transitions = []
        for city_idx in range(5):
            city = cities[city_idx]
            for neighbor in adjacency[city]:
                neighbor_idx = city_map[neighbor]
                possible_transitions.append(And(current_city == city_idx, next_city == neighbor_idx))
        solver.add(Or(same_city, Or(possible_transitions)))

    # Total days per city
    required_days = {
        'Frankfurt': 3,
        'Naples': 4,
        'Helsinki': 4,
        'Lyon': 3,
        'Prague': 2
    }
    for city, days in required_days.items():
        city_idx = city_map[city]
        solver.add(Sum([If(day == city_idx, 1, 0) for day in day_to_city]) == days)

    # Helsinki must be visited from day 2 to day 5 (inclusive)
    for day in [1, 2, 3, 4]:  # days 2 to 5 (1-based)
        solver.add(day_to_city[day] == city_map['Helsinki'])

    # Prague workshop between day 1 and day 2: either day 1 or day 2 is Prague
    solver.add(Or(day_to_city[0] == city_map['Prague'], day_to_city[1] == city_map['Prague']))

    # Check if the problem is solvable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(n_days):
            city_idx = model.evaluate(day_to_city[i]).as_long()
            itinerary.append({'day': i + 1, 'place': cities[city_idx]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Output the result as JSON
import json
result = solve_itinerary()
print(json.dumps(result, indent=2))
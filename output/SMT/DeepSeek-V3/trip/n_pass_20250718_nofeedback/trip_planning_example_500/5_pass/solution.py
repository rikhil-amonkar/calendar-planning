from z3 import *

def solve_itinerary():
    # Define the cities
    cities = ['Hamburg', 'Munich', 'Manchester', 'Lyon', 'Split']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_days = 20
    n_cities = len(cities)

    # Direct flights: adjacency list
    direct_flights = {
        'Split': ['Munich', 'Lyon', 'Hamburg'],
        'Munich': ['Split', 'Manchester', 'Hamburg', 'Lyon'],
        'Manchester': ['Munich', 'Hamburg', 'Split'],
        'Hamburg': ['Manchester', 'Munich', 'Split'],
        'Lyon': ['Split', 'Munich']
    }

    # Create Z3 variables: day[i] is the city index for day i+1 (days are 1-based)
    day = [Int(f'day_{i}') for i in range(n_days)]

    # Create a solver
    solver = Solver()

    # Each day must be a valid city index (0 to n_cities-1)
    for d in day:
        solver.add(And(d >= 0, d < n_cities))

    # Constraints for transitions: adjacent days must be either same city or connected by direct flight
    for i in range(n_days - 1):
        current_city = day[i]
        next_city = day[i + 1]
        # Either stay in the same city or move to a directly connected city
        same_city = (current_city == next_city)
        possible_flights = []
        for city_idx in range(n_cities):
            current_city_name = cities[city_idx]
            connected_cities = direct_flights.get(current_city_name, [])
            for target_city in connected_cities:
                target_idx = city_map[target_city]
                possible_flights.append(And(current_city == city_idx, next_city == target_idx))
        solver.add(Or(same_city, Or(possible_flights)))

    # Total days per city constraints
    total_days = [0]*n_cities
    for city_idx in range(n_cities):
        total_days[city_idx] = Sum([If(day[d] == city_idx, 1, 0) for d in range(n_days)])
    solver.add(total_days[city_map['Hamburg']] == 7)
    solver.add(total_days[city_map['Munich']] == 6)
    solver.add(total_days[city_map['Manchester']] == 2)
    solver.add(total_days[city_map['Lyon']] == 2)
    solver.add(total_days[city_map['Split']] == 7)

    # Fixed constraints:
    # Manchester between day 19 and 20 (inclusive)
    solver.add(Or(day[18] == city_map['Manchester'], day[19] == city_map['Manchester']))
    # Lyon on day 13 and 14 (1-based, so indices 12 and 13)
    solver.add(day[12] == city_map['Lyon'])
    solver.add(day[13] == city_map['Lyon'])

    # Check and get the model
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for d in range(n_days):
            city_idx = model.evaluate(day[d]).as_long()
            itinerary.append({'day': d + 1, 'city': cities[city_idx]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Generate and print the itinerary
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))
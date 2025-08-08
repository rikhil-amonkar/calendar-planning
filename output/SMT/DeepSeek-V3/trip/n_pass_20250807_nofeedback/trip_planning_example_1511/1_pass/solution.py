from z3 import *

def solve_itinerary():
    # Define the cities with unique identifiers
    cities = {
        'Venice': 0,
        'Reykjavik': 1,
        'Munich': 2,
        'Santorini': 3,
        'Manchester': 4,
        'Porto': 5,
        'Bucharest': 6,
        'Tallinn': 7,
        'Valencia': 8,
        'Vienna': 9
    }
    num_cities = len(cities)
    num_days = 24

    # Direct flights: adjacency list
    direct_flights = {
        cities['Bucharest']: [cities['Manchester'], cities['Valencia'], cities['Vienna'], cities['Munich']],
        cities['Manchester']: [cities['Bucharest'], cities['Santorini'], cities['Vienna'], cities['Venice'], cities['Porto'], cities['Munich']],
        cities['Munich']: [cities['Venice'], cities['Porto'], cities['Manchester'], cities['Reykjavik'], cities['Vienna'], cities['Valencia'], cities['Bucharest'], cities['Tallinn']],
        cities['Santorini']: [cities['Manchester'], cities['Venice'], cities['Vienna'], cities['Bucharest']],
        cities['Vienna']: [cities['Reykjavik'], cities['Valencia'], cities['Manchester'], cities['Porto'], cities['Venice'], cities['Santorini'], cities['Bucharest'], cities['Munich']],
        cities['Venice']: [cities['Munich'], cities['Santorini'], cities['Manchester'], cities['Vienna']],
        cities['Reykjavik']: [cities['Vienna'], cities['Munich']],
        cities['Porto']: [cities['Munich'], cities['Vienna'], cities['Manchester'], cities['Valencia']],
        cities['Valencia']: [cities['Vienna'], cities['Bucharest'], cities['Porto'], cities['Munich']],
        cities['Tallinn']: [cities['Munich']]
    }

    # Create Z3 variables: day[i] is the city visited on day i+1 (days are 1-based)
    day = [Int(f'day_{i}') for i in range(num_days)]

    # Create a solver instance
    s = Solver()

    # Constraint: each day's city must be one of the 10 cities
    for d in day:
        s.add(Or([d == c for c in cities.values()]))

    # Fixed day constraints
    # Munich from day 4 to 6 (inclusive)
    s.add(day[3] == cities['Munich'])
    s.add(day[4] == cities['Munich'])
    s.add(day[5] == cities['Munich'])

    # Santorini between day 8 and 10 (inclusive)
    s.add(Or([day[7] == cities['Santorini'], day[8] == cities['Santorini'], day[9] == cities['Santorini']]))

    # Valencia between day 14 and 15 (inclusive)
    s.add(Or(day[13] == cities['Valencia'], day[14] == cities['Valencia']))

    # Flight transitions: consecutive days must be same city or have a direct flight
    for i in range(num_days - 1):
        current_city = day[i]
        next_city = day[i+1]
        s.add(Or(
            current_city == next_city,
            And([Implies(current_city == c1, Or([next_city == c2 for c2 in direct_flights.get(c1, [])])) for c1 in direct_flights.keys()])
        ))

    # Duration constraints for each city
    # Venice: 3 days
    s.add(Sum([If(day[i] == cities['Venice'], 1, 0) for i in range(num_days)]) == 3)
    # Reykjavik: 2 days
    s.add(Sum([If(day[i] == cities['Reykjavik'], 1, 0) for i in range(num_days)]) == 2)
    # Munich: 3 days (already fixed days 4-6)
    # Santorini: 3 days
    s.add(Sum([If(day[i] == cities['Santorini'], 1, 0) for i in range(num_days)]) == 3)
    # Manchester: 3 days
    s.add(Sum([If(day[i] == cities['Manchester'], 1, 0) for i in range(num_days)]) == 3)
    # Porto: 3 days
    s.add(Sum([If(day[i] == cities['Porto'], 1, 0) for i in range(num_days)]) == 3)
    # Bucharest: 5 days
    s.add(Sum([If(day[i] == cities['Bucharest'], 1, 0) for i in range(num_days)]) == 5)
    # Tallinn: 4 days
    s.add(Sum([If(day[i] == cities['Tallinn'], 1, 0) for i in range(num_days)]) == 4)
    # Valencia: 2 days (including the workshop days)
    s.add(Sum([If(day[i] == cities['Valencia'], 1, 0) for i in range(num_days)]) == 2)
    # Vienna: 5 days
    s.add(Sum([If(day[i] == cities['Vienna'], 1, 0) for i in range(num_days)]) == 5)

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        city_names = {v: k for k, v in cities.items()}
        for i in range(num_days):
            city_code = model.evaluate(day[i]).as_long()
            itinerary.append({'day': i+1, 'place': city_names[city_code]})
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")
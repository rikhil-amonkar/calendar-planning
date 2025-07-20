import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = ['Frankfurt', 'Manchester', 'Valencia', 'Naples', 'Oslo', 'Vilnius']
    required_days = {
        'Frankfurt': 4,
        'Manchester': 4,
        'Valencia': 4,
        'Naples': 4,
        'Oslo': 3,
        'Vilnius': 2
    }
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_cities = len(cities)
    n_days = 16

    # Direct flight connections
    direct_flights = [
        [False] * n_cities for _ in range(n_cities)
    ]
    connections = [
        ('Valencia', 'Frankfurt'),
        ('Manchester', 'Frankfurt'),
        ('Naples', 'Manchester'),
        ('Naples', 'Frankfurt'),
        ('Naples', 'Oslo'),
        ('Oslo', 'Frankfurt'),
        ('Vilnius', 'Frankfurt'),
        ('Oslo', 'Vilnius'),
        ('Manchester', 'Oslo'),
        ('Valencia', 'Naples')
    ]
    for c1, c2 in connections:
        i, j = city_map[c1], city_map[c2]
        direct_flights[i][j] = True
        direct_flights[j][i] = True

    # Create Z3 solver
    s = Solver()

    # Decision variables: for each day, which city are we in
    assignments = [Int(f'day_{i}') for i in range(n_days)]
    for a in assignments:
        s.add(a >= 0, a < n_cities)

    # Each city must be visited for exactly the required number of days
    for city, days in required_days.items():
        c = city_map[city]
        s.add(Sum([If(assignments[i] == c, 1, 0) for i in range(n_days)]) == days)

    # Flight transition constraints
    for i in range(n_days - 1):
        current = assignments[i]
        next_day = assignments[i + 1]
        # Either stay in same city or take direct flight
        s.add(Or(
            current == next_day,
            *[And(current == c1, next_day == c2) 
              for c1 in range(n_cities) 
              for c2 in range(n_cities) 
              if direct_flights[c1][c2]
        ))

    # Special constraints:
    # Frankfurt from day 13 to 16 (indices 12 to 15)
    for i in range(12, 16):
        s.add(assignments[i] == city_map['Frankfurt'])

    # Vilnius wedding on days 12 and 13 (indices 11 and 12)
    s.add(assignments[11] == city_map['Vilnius'])
    s.add(assignments[12] == city_map['Vilnius'])

    # Find solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(n_days):
            city_idx = model[assignments[i]].as_long()
            itinerary.append({"day": i+1, "place": cities[city_idx]})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))
import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Frankfurt', 'Manchester', 'Valencia', 'Naples', 'Oslo', 'Vilnius']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_cities = len(cities)
    n_days = 16

    # Direct flights: adjacency matrix
    direct_flights = [[False] * n_cities for _ in range(n_cities)]
    # Valencia and Frankfurt
    direct_flights[city_map['Valencia']][city_map['Frankfurt']] = True
    direct_flights[city_map['Frankfurt']][city_map['Valencia']] = True
    # Manchester and Frankfurt
    direct_flights[city_map['Manchester']][city_map['Frankfurt']] = True
    direct_flights[city_map['Frankfurt']][city_map['Manchester']] = True
    # Naples and Manchester
    direct_flights[city_map['Naples']][city_map['Manchester']] = True
    direct_flights[city_map['Manchester']][city_map['Naples']] = True
    # Naples and Frankfurt
    direct_flights[city_map['Naples']][city_map['Frankfurt']] = True
    direct_flights[city_map['Frankfurt']][city_map['Naples']] = True
    # Naples and Oslo
    direct_flights[city_map['Naples']][city_map['Oslo']] = True
    direct_flights[city_map['Oslo']][city_map['Naples']] = True
    # Oslo and Frankfurt
    direct_flights[city_map['Oslo']][city_map['Frankfurt']] = True
    direct_flights[city_map['Frankfurt']][city_map['Oslo']] = True
    # Vilnius and Frankfurt
    direct_flights[city_map['Vilnius']][city_map['Frankfurt']] = True
    direct_flights[city_map['Frankfurt']][city_map['Vilnius']] = True
    # Oslo and Vilnius
    direct_flights[city_map['Oslo']][city_map['Vilnius']] = True
    direct_flights[city_map['Vilnius']][city_map['Oslo']] = True
    # Manchester and Oslo
    direct_flights[city_map['Manchester']][city_map['Oslo']] = True
    direct_flights[city_map['Oslo']][city_map['Manchester']] = True
    # Valencia and Naples
    direct_flights[city_map['Valencia']][city_map['Naples']] = True
    direct_flights[city_map['Naples']][city_map['Valencia']] = True

    # Z3 solver
    s = Solver()

    # Variables: day i is in city c
    assignments = [[Bool(f"day_{i}_city_{c}") for c in range(n_cities)] for i in range(n_days)]

    # Each day is in exactly one city
    for i in range(n_days):
        s.add(Or([assignments[i][c] for c in range(n_cities)]))
        for c1 in range(n_cities):
            for c2 in range(c1 + 1, n_cities):
                s.add(Or(Not(assignments[i][c1]), Not(assignments[i][c2])))

    # Transition constraints
    for i in range(n_days - 1):
        for c1 in range(n_cities):
            for c2 in range(n_cities):
                if c1 != c2:
                    s.add(Implies(
                        And(assignments[i][c1], assignments[i+1][c2]),
                        direct_flights[c1][c2]
                    ))

    # City day counts
    city_days = [
        ('Frankfurt', 4),
        ('Manchester', 4),
        ('Valencia', 4),
        ('Naples', 4),
        ('Oslo', 3),
        ('Vilnius', 2)
    ]
    for city, total in city_days:
        c = city_map[city]
        s.add(Sum([If(assignments[i][c], 1, 0) for i in range(n_days)]) == total)

    # Frankfurt from day 13 to 16 (indices 12 to 15)
    for i in range(12, 16):
        s.add(assignments[i][city_map['Frankfurt']])

    # Vilnius wedding between day 12 and 13 (indices 11 and 12)
    s.add(assignments[11][city_map['Vilnius']])
    s.add(assignments[12][city_map['Vilnius']])

    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(n_days):
            for c in range(n_cities):
                if is_true(model.eval(assignments[i][c])):
                    itinerary.append({"day": i+1, "place": cities[c]})
                    break
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))
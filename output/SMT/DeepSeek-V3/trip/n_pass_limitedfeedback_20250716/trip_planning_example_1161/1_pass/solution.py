from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Mykonos', 'Krakow', 'Vilnius', 'Helsinki', 'Dubrovnik', 'Oslo', 'Madrid', 'Paris']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_cities = len(cities)
    n_days = 18

    # Flight connections: list of tuples (from, to)
    flights = [
        ('Oslo', 'Krakow'), ('Oslo', 'Paris'), ('Paris', 'Madrid'),
        ('Helsinki', 'Vilnius'), ('Oslo', 'Madrid'), ('Oslo', 'Helsinki'),
        ('Helsinki', 'Krakow'), ('Dubrovnik', 'Helsinki'), ('Dubrovnik', 'Madrid'),
        ('Oslo', 'Dubrovnik'), ('Krakow', 'Paris'), ('Madrid', 'Mykonos'),
        ('Oslo', 'Vilnius'), ('Krakow', 'Vilnius'), ('Helsinki', 'Paris'),
        ('Vilnius', 'Paris'), ('Helsinki', 'Madrid')
    ]
    # Make flights bidirectional
    flight_pairs = set()
    for a, b in flights:
        flight_pairs.add((city_map[a], city_map[b]))
        flight_pairs.add((city_map[b], city_map[a]))
    
    # Z3 variables: day i is in city c
    X = [[Bool(f"day_{i}_city_{c}") for c in range(n_cities)] for i in range(n_days)]
    s = Solver()

    # Each day is exactly in one city
    for i in range(n_days):
        s.add(Or([X[i][c] for c in range(n_cities)]))
        for c1 in range(n_cities):
            for c2 in range(c1 + 1, n_cities):
                s.add(Not(And(X[i][c1], X[i][c2])))

    # Flight constraints: consecutive days must be same city or connected by flight
    for i in range(n_days - 1):
        for c1 in range(n_cities):
            for c2 in range(n_cities):
                if c1 != c2:
                    # If day i is c1 and day i+1 is c2, then (c1,c2) must be in flight_pairs
                    s.add(Implies(And(X[i][c1], X[i+1][c2]), (c1, c2) in flight_pairs))

    # City day constraints
    # Mykonos: 4 days, between day 15-18 (inclusive)
    mykonos_days = []
    for i in range(15 - 1, 18):  # days are 0-based in code, 1-based in problem
        mykonos_days.append(X[i][city_map['Mykonos']])
    s.add(Sum([If(cond, 1, 0) for cond in mykonos_days]) >= 4)
    # Actually, Mykonos must be visited for exactly 4 days between day 15-18. So sum is 4.
    s.add(Sum([If(cond, 1, 0) for cond in mykonos_days]) == 4)

    # Krakow: 5 days
    krakow_days = [X[i][city_map['Krakow']] for i in range(n_days)]
    s.add(Sum([If(cond, 1, 0) for cond in krakow_days]) == 5)

    # Vilnius: 2 days
    vilnius_days = [X[i][city_map['Vilnius']] for i in range(n_days)]
    s.add(Sum([If(cond, 1, 0) for cond in vilnius_days]) == 2)

    # Helsinki: 2 days
    helsinki_days = [X[i][city_map['Helsinki']] for i in range(n_days)]
    s.add(Sum([If(cond, 1, 0) for cond in helsinki_days]) == 2)

    # Dubrovnik: 3 days, including days 2-4 (1-based) which are days 1-3 (0-based)
    dubrovnik_days = [X[i][city_map['Dubrovnik']] for i in range(n_days)]
    s.add(Sum([If(cond, 1, 0) for cond in dubrovnik_days]) == 3)
    # Days 2-4 (1-3 0-based) must be in Dubrovnik
    for i in range(1, 4):
        s.add(X[i][city_map['Dubrovnik']])

    # Oslo: 2 days, and meet friends between day 1 and 2 (0-based days 0 and 1)
    oslo_days = [X[i][city_map['Oslo']] for i in range(n_days)]
    s.add(Sum([If(cond, 1, 0) for cond in oslo_days]) == 2)
    s.add(Or(X[0][city_map['Oslo']], X[1][city_map['Oslo']]))

    # Madrid: 5 days
    madrid_days = [X[i][city_map['Madrid']] for i in range(n_days)]
    s.add(Sum([If(cond, 1, 0) for cond in madrid_days]) == 5)

    # Paris: 2 days
    paris_days = [X[i][city_map['Paris']] for i in range(n_days)]
    s.add(Sum([If(cond, 1, 0) for cond in paris_days]) == 2)

    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n_days):
            for c in range(n_cities):
                if m.evaluate(X[i][c]):
                    itinerary.append({"day": i + 1, "place": cities[c]})
                    break
        # Verify days per city
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['place']] += 1
        # Print for verification
        print("City days:", city_days)
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))
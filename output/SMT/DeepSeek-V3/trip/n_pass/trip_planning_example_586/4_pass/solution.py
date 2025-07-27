from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Frankfurt', 'Naples', 'Helsinki', 'Lyon', 'Prague']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_days = 12
    n_cities = len(cities)

    # Direct flights: adjacency matrix
    direct_flights = [
        [False, True, True, True, True],   # Frankfurt (0) connected to Naples(1), Helsinki(2), Lyon(3), Prague(4)
        [True, False, True, False, False],  # Naples (1) connected to Frankfurt, Helsinki
        [True, True, False, False, True],   # Helsinki (2) connected to Frankfurt, Naples, Prague
        [True, False, False, False, True],  # Lyon (3) connected to Frankfurt, Prague
        [True, False, True, True, False]    # Prague (4) connected to Frankfurt, Helsinki, Lyon
    ]

    # Z3 variables: day i is in city j
    X = [[Bool(f"day_{i}_city_{j}") for j in range(n_cities)] for i in range(n_days)]

    s = Solver()

    # Each day is in exactly one city
    for i in range(n_days):
        s.add(Or([X[i][j] for j in range(n_cities)]))  # At least one city per day
        # No two cities on the same day
        for j1 in range(n_cities):
            for j2 in range(j1 + 1, n_cities):
                s.add(Or(Not(X[i][j1]), Not(X[i][j2])))

    # City day constraints
    # Frankfurt: 3 days
    frankfurt_days = Sum([If(X[i][city_map['Frankfurt']], 1, 0) for i in range(n_days)])
    s.add(frankfurt_days == 3)
    # Naples: 4 days
    naples_days = Sum([If(X[i][city_map['Naples']], 1, 0) for i in range(n_days)])
    s.add(naples_days == 4)
    # Helsinki: 4 days (must include days 2-5)
    helsinki_days = Sum([If(X[i][city_map['Helsinki']], 1, 0) for i in range(n_days)])
    s.add(helsinki_days == 4)
    for i in [1, 2, 3, 4]:  # days 2-5 (0-based day 1 is day 2 in problem)
        s.add(X[i][city_map['Helsinki']])
    # Lyon: 3 days
    lyon_days = Sum([If(X[i][city_map['Lyon']], 1, 0) for i in range(n_days)])
    s.add(lyon_days == 3)
    # Prague: 2 days, including day 0 or 1 (days 1 and 2 in problem description)
    prague_days = Sum([If(X[i][city_map['Prague']], 1, 0) for i in range(n_days)])
    s.add(prague_days == 2)
    s.add(Or(X[0][city_map['Prague']], X[1][city_map['Prague']]))

    # Flight constraints: consecutive days in different cities must have a direct flight
    for i in range(n_days - 1):
        for j1 in range(n_cities):
            for j2 in range(n_cities):
                if j1 != j2:
                    # If day i is city j1 and day i+1 is city j2, then there must be a direct flight
                    s.add(Implies(And(X[i][j1], X[i+1][j2]), direct_flights[j1][j2]))

    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n_days):
            for j in range(n_cities):
                if m.evaluate(X[i][j]):
                    itinerary.append({"day": i+1, "place": cities[j]})
        # Verify the counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry["place"]] += 1
        # Check if counts meet requirements
        assert counts['Frankfurt'] == 3
        assert counts['Naples'] == 4
        assert counts['Helsinki'] == 4
        assert counts['Lyon'] == 3
        assert counts['Prague'] == 2
        # Check Helsinki days 2-5
        helsinki_days = [entry['day'] for entry in itinerary if entry['place'] == 'Helsinki']
        assert all(day in helsinki_days for day in [2, 3, 4, 5])
        # Check Prague day 1 or 2
        prague_days = [entry['day'] for entry in itinerary if entry['place'] == 'Prague']
        assert any(day in [1, 2] for day in prague_days)
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))
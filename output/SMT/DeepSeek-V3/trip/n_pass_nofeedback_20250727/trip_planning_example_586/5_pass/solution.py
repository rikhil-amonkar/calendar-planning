from z3 import *

def solve_itinerary():
    # Cities and their mappings
    cities = ['Frankfurt', 'Naples', 'Helsinki', 'Lyon', 'Prague']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_days = 12
    n_cities = len(cities)

    # Direct flights adjacency matrix
    direct_flights = [
        [False, True, True, True, True],    # Frankfurt
        [True, False, True, False, False],  # Naples
        [True, True, False, False, True],   # Helsinki
        [True, False, False, False, True],  # Lyon
        [True, False, True, True, False]    # Prague
    ]

    # Create Z3 variables for each day and city
    X = [[Bool(f"day_{i}_city_{j}") for j in range(n_cities)] for i in range(n_days)]
    
    s = Solver()

    # Each day must be in exactly one city
    for i in range(n_days):
        s.add(Or([X[i][j] for j in range(n_cities)]))
        for j1 in range(n_cities):
            for j2 in range(j1 + 1, n_cities):
                s.add(Or(Not(X[i][j1]), Not(X[i][j2])))

    # City day constraints
    s.add(Sum([If(X[i][city_map['Frankfurt']], 1, 0) for i in range(n_days)]) == 3)
    s.add(Sum([If(X[i][city_map['Naples']], 1, 0) for i in range(n_days)]) == 4)
    s.add(Sum([If(X[i][city_map['Helsinki']], 1, 0) for i in range(n_days)]) == 4)
    s.add(Sum([If(X[i][city_map['Lyon']], 1, 0) for i in range(n_days)]) == 3)
    s.add(Sum([If(X[i][city_map['Prague']], 1, 0) for i in range(n_days)]) == 2)

    # Event constraints
    # Helsinki days 2-5 (1-4 in 0-based)
    for i in [1, 2, 3, 4]:
        s.add(X[i][city_map['Helsinki']])
    # Prague on day 1 or 2 (0 or 1 in 0-based)
    s.add(Or(X[0][city_map['Prague']], X[1][city_map['Prague']]))

    # Flight constraints - transitions must be direct flights
    for i in range(n_days - 1):
        for j1 in range(n_cities):
            for j2 in range(n_cities):
                if j1 != j2:
                    s.add(Implies(And(X[i][j1], X[i+1][j2]), direct_flights[j1][j2]))

    # Solve and get itinerary
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n_days):
            for j in range(n_cities):
                if m.evaluate(X[i][j]):
                    itinerary.append({"day": i+1, "place": cities[j]})
        
        # Verify constraints
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry["place"]] += 1
        
        assert counts['Frankfurt'] == 3
        assert counts['Naples'] == 4
        assert counts['Helsinki'] == 4
        assert counts['Lyon'] == 3
        assert counts['Prague'] == 2
        
        helsinki_days = [entry['day'] for entry in itinerary if entry['place'] == 'Helsinki']
        assert all(day in helsinki_days for day in [2, 3, 4, 5])
        
        prague_days = [entry['day'] for entry in itinerary if entry['place'] == 'Prague']
        assert any(day in [1, 2] for day in prague_days)
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))
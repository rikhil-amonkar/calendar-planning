from z3 import *

def solve_itinerary():
    # Cities with indices
    cities = ['Mykonos', 'Krakow', 'Vilnius', 'Helsinki', 'Dubrovnik', 'Oslo', 'Madrid', 'Paris']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_cities = len(cities)
    n_days = 18

    # Flight connections (bidirectional)
    flight_pairs = [
        (city_map['Oslo'], city_map['Krakow']),
        (city_map['Oslo'], city_map['Paris']),
        (city_map['Paris'], city_map['Madrid']),
        (city_map['Helsinki'], city_map['Vilnius']),
        (city_map['Oslo'], city_map['Madrid']),
        (city_map['Oslo'], city_map['Helsinki']),
        (city_map['Helsinki'], city_map['Krakow']),
        (city_map['Dubrovnik'], city_map['Helsinki']),
        (city_map['Dubrovnik'], city_map['Madrid']),
        (city_map['Oslo'], city_map['Dubrovnik']),
        (city_map['Krakow'], city_map['Paris']),
        (city_map['Madrid'], city_map['Mykonos']),
        (city_map['Oslo'], city_map['Vilnius']),
        (city_map['Krakow'], city_map['Vilnius']),
        (city_map['Helsinki'], city_map['Paris']),
        (city_map['Vilnius'], city_map['Paris']),
        (city_map['Helsinki'], city_map['Madrid'])
    ]
    # Make bidirectional
    flight_pairs += [(b, a) for (a, b) in flight_pairs]
    flight_matrix = [[False]*n_cities for _ in range(n_cities)]
    for a, b in flight_pairs:
        flight_matrix[a][b] = True

    # Create solver
    s = Solver()

    # Variables: city each day (0-7)
    X = [Int(f'day_{i}') for i in range(n_days)]
    for x in X:
        s.add(x >= 0, x < n_cities)

    # Flight constraints between consecutive days
    for i in range(n_days - 1):
        s.add(Or(
            X[i] == X[i+1],  # Stay in same city
            flight_matrix[X[i]][X[i+1]]  # Or take valid flight
        ))

    # City duration constraints
    for city in cities:
        idx = city_map[city]
        s.add(Sum([If(X[i] == idx, 1, 0) for i in range(n_days)]) == {
            'Mykonos': 4,
            'Krakow': 5,
            'Vilnius': 2,
            'Helsinki': 2,
            'Dubrovnik': 3,
            'Oslo': 2,
            'Madrid': 5,
            'Paris': 2
        }[city])

    # Fixed visits
    # Dubrovnik days 2-4 (1-3 in 0-based)
    for i in range(1, 4):
        s.add(X[i] == city_map['Dubrovnik'])
    # Oslo days 1-2 (0-1 in 0-based)
    s.add(Or(X[0] == city_map['Oslo'], X[1] == city_map['Oslo']))
    # Mykonos days 15-18 (14-17 in 0-based)
    s.add(Sum([If(X[i] == city_map['Mykonos'], 1, 0) for i in range(14, 18)]) == 4)

    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n_days):
            city_idx = m.evaluate(X[i]).as_long()
            itinerary.append({"day": i+1, "place": cities[city_idx]})
        
        # Verify constraints
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['place']] += 1
        print("Verification:", city_days)
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))
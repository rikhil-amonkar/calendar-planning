from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Dublin', 'Krakow', 'Istanbul', 'Venice', 'Naples', 'Brussels', 'Mykonos', 'Frankfurt']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: list of tuples (from, to)
    direct_flights = [
        ('Dublin', 'Brussels'), ('Mykonos', 'Naples'), ('Venice', 'Istanbul'),
        ('Frankfurt', 'Krakow'), ('Naples', 'Dublin'), ('Krakow', 'Brussels'),
        ('Naples', 'Istanbul'), ('Naples', 'Brussels'), ('Istanbul', 'Frankfurt'),
        ('Brussels', 'Frankfurt'), ('Istanbul', 'Krakow'), ('Istanbul', 'Brussels'),
        ('Venice', 'Frankfurt'), ('Naples', 'Frankfurt'), ('Dublin', 'Krakow'),
        ('Venice', 'Brussels'), ('Naples', 'Venice'), ('Istanbul', 'Dublin'),
        ('Venice', 'Dublin'), ('Dublin', 'Frankfurt')
    ]
    
    # Correct any typos in city names
    corrected_flights = []
    for (a, b) in direct_flights:
        if a == 'Naples':
            a = 'Naples'
        if b == 'Naples':
            b = 'Naples'
        corrected_flights.append((a, b))
    direct_flights = corrected_flights
    
    # Flight pairs are bidirectional
    flight_pairs = set()
    for (a, b) in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    # Create Z3 variables: for each day, which city are you in?
    days = 21
    X = [Int(f'X_{i}') for i in range(days)]
    
    s = Solver()
    
    # Each X_i must be between 0 and 7 (city indices)
    for i in range(days):
        s.add(X[i] >= 0, X[i] < len(cities))
    
    # Flight transitions: consecutive days must be same city or connected by a direct flight
    for i in range(days - 1):
        current_city = X[i]
        next_city = X[i + 1]
        # Either stay in the same city or move to a connected city
        same_city = current_city == next_city
        flight_possible = Or([And(current_city == city_to_idx[a], next_city == city_to_idx[b]) 
                            for (a, b) in flight_pairs])
        s.add(Or(same_city, flight_possible))
    
    # Duration constraints
    # Dublin: 5 days total, including days 11-15 (0-based: 10-14)
    dublin_idx = city_to_idx['Dublin']
    s.add(Sum([If(X[i] == dublin_idx, 1, 0) for i in range(days)]) == 5)
    for i in range(10, 15):
        s.add(X[i] == dublin_idx)
    
    # Krakow: 4 days
    krakow_idx = city_to_idx['Krakow']
    s.add(Sum([If(X[i] == krakow_idx, 1, 0) for i in range(days)]) == 4)
    
    # Istanbul: 3 days, including a visit between day 9-11 (0-based: 8-10)
    istanbul_idx = city_to_idx['Istanbul']
    s.add(Sum([If(X[i] == istanbul_idx, 1, 0) for i in range(days)]) == 3)
    s.add(Or([X[i] == istanbul_idx for i in range(8, 11)]))
    
    # Venice: 3 days
    venice_idx = city_to_idx['Venice']
    s.add(Sum([If(X[i] == venice_idx, 1, 0) for i in range(days)]) == 3)
    
    # Naples: 4 days
    naples_idx = city_to_idx['Naples']
    s.add(Sum([If(X[i] == naples_idx, 1, 0) for i in range(days)]) == 4)
    
    # Brussels: 2 days
    brussels_idx = city_to_idx['Brussels']
    s.add(Sum([If(X[i] == brussels_idx, 1, 0) for i in range(days)]) == 2)
    
    # Mykonos: 4 days, between day 1-4 (0-based: 0-3)
    mykonos_idx = city_to_idx['Mykonos']
    s.add(Sum([If(X[i] == mykonos_idx, 1, 0) for i in range(days)]) == 4)
    s.add(Or([X[i] == mykonos_idx for i in range(0, 4)]))
    
    # Frankfurt: 3 days, between day 15-17 (0-based: 14-16)
    frankfurt_idx = city_to_idx['Frankfurt']
    s.add(Sum([If(X[i] == frankfurt_idx, 1, 0) for i in range(days)]) == 3)
    s.add(Or([X[i] == frankfurt_idx for i in range(14, 17)]))
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            city_idx = model.evaluate(X[i]).as_long()
            itinerary.append({'day': i + 1, 'city': cities[city_idx]})
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the solver
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))
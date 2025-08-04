from z3 import *

def solve_trip_scheduling():
    # Cities
    cities = ['Geneva', 'Munich', 'Valencia', 'Bucharest', 'Stuttgart']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_days = 17
    n_cities = len(cities)
    
    # Direct flights: adjacency list
    adjacency = {
        'Geneva': ['Munich', 'Valencia'],
        'Munich': ['Geneva', 'Valencia', 'Bucharest'],
        'Valencia': ['Geneva', 'Munich', 'Bucharest', 'Stuttgart'],
        'Bucharest': ['Munich', 'Valencia'],
        'Stuttgart': ['Valencia']
    }
    
    # Create adjacency matrix for Z3 constraints
    connected = [[False for _ in range(n_cities)] for _ in range(n_cities)]
    for city in adjacency:
        for neighbor in adjacency[city]:
            i = city_map[city]
            j = city_map[neighbor]
            connected[i][j] = True
            connected[j][i] = True
    
    # Z3 variables: for each day, which city (0..n_cities-1)
    X = [Int(f'X_{i}') for i in range(n_days)]
    
    s = Solver()
    
    # Each day's city must be valid (0 <= X_i < n_cities)
    for i in range(n_days):
        s.add(And(X[i] >= 0, X[i] < n_cities))
    
    # Flight constraints: consecutive days must be connected
    for i in range(n_days - 1):
        current_city = X[i]
        next_city = X[i + 1]
        # Add constraint that connected[current_city][next_city] is True
        constraints = []
        for c1 in range(n_cities):
            for c2 in range(n_cities):
                if connected[c1][c2]:
                    constraints.append(And(current_city == c1, next_city == c2))
        s.add(Or(constraints))
    
    # Days in each city
    # Geneva: 4 days (including flight days)
    geneva_days = Sum([If(X[i] == city_map['Geneva'], 1, 0) for i in range(n_days)])
    s.add(geneva_days == 4)
    
    # Munich: 7 days
    munich_days = Sum([If(X[i] == city_map['Munich'], 1, 0) for i in range(n_days)])
    s.add(munich_days == 7)
    
    # Valencia: 6 days
    valencia_days = Sum([If(X[i] == city_map['Valencia'], 1, 0) for i in range(n_days)])
    s.add(valencia_days == 6)
    
    # Bucharest: 2 days
    bucharest_days = Sum([If(X[i] == city_map['Bucharest'], 1, 0) for i in range(n_days)])
    s.add(bucharest_days == 2)
    
    # Stuttgart: 2 days
    stuttgart_days = Sum([If(X[i] == city_map['Stuttgart'], 1, 0) for i in range(n_days)])
    s.add(stuttgart_days == 2)
    
    # Geneva must be visited between day 1 and 4 (1-based, so days 0-3 in 0-based)
    geneva_in_first_part = Or([X[i] == city_map['Geneva'] for i in range(4)])
    s.add(geneva_in_first_part)
    
    # Munich must be visited between day 4 and 10 (1-based: days 4-10 are 3-9 in 0-based)
    munich_in_window = Or([X[i] == city_map['Munich'] for i in range(3, 10)])
    s.add(munich_in_window)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n_days):
            city_idx = m.evaluate(X[i]).as_long()
            city = cities[city_idx]
            itinerary.append({'day': i + 1, 'place': city})
        
        # Verify days per city
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['place']] += 1
        
        print("City days verification:", city_days)
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_trip_scheduling()
print(result)
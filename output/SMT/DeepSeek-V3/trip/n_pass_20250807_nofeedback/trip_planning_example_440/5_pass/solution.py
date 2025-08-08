from z3 import *

def solve_itinerary():
    # Cities represented as integers
    cities = {
        'Split': 0,
        'Helsinki': 1,
        'Reykjavik': 2,
        'Vilnius': 3,
        'Geneva': 4
    }
    city_names = ['Split', 'Helsinki', 'Reykjavik', 'Vilnius', 'Geneva']
    n_cities = len(cities)
    
    # Direct flights: adjacency list (bidirectional)
    direct_flights = {
        0: [1, 3, 4],  # Split
        1: [0, 2, 3, 4],  # Helsinki
        2: [1],  # Reykjavik
        3: [0, 1],  # Vilnius
        4: [0, 1]  # Geneva
    }
    
    # Create Z3 solver
    s = Solver()
    
    # Day variables (0-based)
    days = [Int(f'day_{i}') for i in range(12)]
    for day in days:
        s.add(day >= 0, day < n_cities)
    
    # Duration constraints
    s.add(Sum([If(d == cities['Split'], 1, 0) for d in days]) == 2)
    s.add(Sum([If(d == cities['Helsinki'], 1, 0) for d in days]) == 2)
    s.add(Sum([If(d == cities['Reykjavik'], 1, 0) for d in days]) == 3)
    s.add(Sum([If(d == cities['Vilnius'], 1, 0) for d in days]) == 3)
    s.add(Sum([If(d == cities['Geneva'], 1, 0) for d in days]) == 6)
    
    # Fixed date constraints (1-based days 10-12 are 0-based 9-11)
    s.add(days[9] == cities['Reykjavik'])
    s.add(days[10] == cities['Reykjavik'])
    s.add(days[11] == cities['Reykjavik'])
    
    # Fixed date constraints (1-based days 7-9 are 0-based 6-8)
    s.add(days[6] == cities['Vilnius'])
    s.add(days[7] == cities['Vilnius'])
    s.add(days[8] == cities['Vilnius'])
    
    # Flight transition constraints
    for i in range(11):
        current = days[i]
        next_day = days[i+1]
        # Either stay or fly directly
        constraints = [current == next_day]
        for city in direct_flights:
            for neighbor in direct_flights[city]:
                constraints.append(And(current == city, next_day == neighbor))
        s.add(Or(*constraints))
    
    # Solve and format output
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(12):
            day_num = i + 1
            city_idx = m.evaluate(days[i]).as_long()
            itinerary.append({'day': day_num, 'place': city_names[city_idx]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))
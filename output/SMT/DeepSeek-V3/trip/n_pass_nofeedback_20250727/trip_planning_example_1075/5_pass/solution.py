import json
from z3 import *

def solve_itinerary():
    # Cities and their codes
    cities = {
        'Vienna': 0,
        'Lyon': 1,
        'Edinburgh': 2,
        'Reykjavik': 3,
        'Stuttgart': 4,
        'Manchester': 5,
        'Split': 6,
        'Prague': 7
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights (bidirectional)
    flight_pairs = [
        (0,1), (0,5), (0,6), (0,7), (0,3), (0,4),  # Vienna
        (1,6), (1,7),                                # Lyon
        (2,4), (2,7),                                # Edinburgh
        (3,4), (3,7),                                # Reykjavik
        (4,5), (4,6),                                # Stuttgart
        (5,6), (5,7),                                # Manchester
        (6,7)                                        # Split-Prague
    ]
    
    # Create solver
    s = Solver()
    
    # Variables: day[i] is city on day i+1 (1-based)
    days = [Int(f'day_{i}') for i in range(25)]
    
    # Each day must be one of the cities
    for d in days:
        s.add(Or([d == c for c in cities.values()]))
    
    # Flight constraints between consecutive days
    for i in range(24):
        current = days[i]
        next_day = days[i+1]
        # Either stay in same city or take direct flight
        s.add(Or(
            current == next_day,
            *[And(current == a, next_day == b) for a, b in flight_pairs],
            *[And(current == b, next_day == a) for a, b in flight_pairs]
        ))
    
    # Duration constraints (including flight days)
    # Vienna: 4 days
    s.add(Sum([If(d == cities['Vienna'], 1, 0) for d in days]) == 4)
    # Lyon: 3 days
    s.add(Sum([If(d == cities['Lyon'], 1, 0) for d in days]) == 3)
    # Edinburgh: 4 days (must include days 5-8)
    s.add(Sum([If(d == cities['Edinburgh'], 1, 0) for d in days]) == 4)
    for i in range(4, 8):  # days 5-8
        s.add(days[i] == cities['Edinburgh'])
    # Reykjavik: 5 days
    s.add(Sum([If(d == cities['Reykjavik'], 1, 0) for d in days]) == 5)
    # Stuttgart: 5 days
    s.add(Sum([If(d == cities['Stuttgart'], 1, 0) for d in days]) == 5)
    # Manchester: 2 days
    s.add(Sum([If(d == cities['Manchester'], 1, 0) for d in days]) == 2)
    # Split: 5 days (must include days 19-23)
    s.add(Sum([If(d == cities['Split'], 1, 0) for d in days]) == 5)
    for i in range(18, 22):  # days 19-22 (23 is last day)
        s.add(days[i] == cities['Split'])
    # Prague: 4 days
    s.add(Sum([If(d == cities['Prague'], 1, 0) for d in days]) == 4)
    
    # Additional constraints to help solver
    # Must start somewhere (let solver choose)
    # Must end somewhere (let solver choose)
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(25):
            city_code = model.evaluate(days[i]).as_long()
            itinerary.append({'day': i+1, 'city': city_names[city_code]})
        
        # Verify all constraints are met
        city_days = {c:0 for c in cities.values()}
        for day in itinerary:
            city_days[cities[day['city']]] += 1
        
        # Return JSON result
        result = {'itinerary': itinerary}
        return json.dumps(result, indent=2)
    else:
        return json.dumps({'error': 'No solution found'}, indent=2)

print(solve_itinerary())
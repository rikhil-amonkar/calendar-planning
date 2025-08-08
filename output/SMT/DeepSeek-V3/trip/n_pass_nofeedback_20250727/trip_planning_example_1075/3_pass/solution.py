import json
from z3 import *

def solve_itinerary():
    # Cities and their codes for easier reference
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
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 5, 6, 7, 3, 4],  # Vienna: Lyon, Manchester, Split, Prague, Reykjavik, Stuttgart
        1: [0, 6, 7],             # Lyon: Vienna, Split, Prague
        2: [4, 7],                # Edinburgh: Stuttgart, Prague
        3: [4, 0, 7],             # Reykjavik: Stuttgart, Vienna, Prague
        4: [3, 0, 2, 5, 6],      # Stuttgart: Reykjavik, Vienna, Edinburgh, Manchester, Split
        5: [7, 6, 0, 4],          # Manchester: Prague, Split, Vienna, Stuttgart
        6: [4, 5, 0, 1, 7],      # Split: Stuttgart, Manchester, Vienna, Lyon, Prague
        7: [0, 1, 2, 3, 5, 6]     # Prague: Vienna, Lyon, Edinburgh, Reykjavik, Manchester, Split
    }
    
    # Create solver
    s = Solver()
    
    # Variables: day[i] is the city visited on day i+1 (days are 1-based)
    days = [Int(f'day_{i}') for i in range(25)]
    
    # Each day must be one of the cities
    for d in days:
        s.add(Or([d == c for c in cities.values()]))
    
    # Flight constraints: consecutive days must be the same city or connected by direct flight
    for i in range(24):
        current_day = days[i]
        next_day = days[i+1]
        # Create a list of possible transitions
        transitions = [current_day == next_day]
        for city in cities.values():
            if city in direct_flights.get(city, []):
                transitions.append(And(current_day == city, next_day in direct_flights[city]))
        s.add(Or(transitions))
    
    # Duration constraints
    # Vienna: 4 days
    s.add(Sum([If(d == cities['Vienna'], 1, 0) for d in days]) == 4)
    # Lyon: 3 days
    s.add(Sum([If(d == cities['Lyon'], 1, 0) for d in days]) == 3)
    # Edinburgh: 4 days, including days 5-8
    s.add(Sum([If(d == cities['Edinburgh'], 1, 0) for d in days]) == 4)
    for i in range(4, 8):  # days 5-8 (0-based 4-7)
        s.add(days[i] == cities['Edinburgh'])
    # Reykjavik: 5 days
    s.add(Sum([If(d == cities['Reykjavik'], 1, 0) for d in days]) == 5)
    # Stuttgart: 5 days
    s.add(Sum([If(d == cities['Stuttgart'], 1, 0) for d in days]) == 5)
    # Manchester: 2 days
    s.add(Sum([If(d == cities['Manchester'], 1, 0) for d in days]) == 2)
    # Split: 5 days, including days 19-23 (0-based 18-22)
    s.add(Sum([If(d == cities['Split'], 1, 0) for d in days]) == 5)
    for i in range(18, 22):
        s.add(days[i] == cities['Split'])
    # Prague: 4 days
    s.add(Sum([If(d == cities['Prague'], 1, 0) for d in days]) == 4)
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(25):
            city_code = model.evaluate(days[i]).as_long()
            itinerary.append({'day': i+1, 'city': city_names[city_code]})
        
        # Convert to required JSON format
        result = {'itinerary': itinerary}
        return json.dumps(result, indent=2)
    else:
        return json.dumps({'error': 'No solution found'}, indent=2)

print(solve_itinerary())
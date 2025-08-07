import json
from z3 import *

def solve_itinerary():
    # Cities and their indices
    cities = ['Oslo', 'Stuttgart', 'Reykjavik', 'Split', 'Geneva', 'Porto', 'Tallinn', 'Stockholm']
    city_idx = {city: i for i, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    flights = {
        'Reykjavik': ['Stuttgart', 'Stockholm', 'Tallinn', 'Oslo'],
        'Stockholm': ['Oslo', 'Stuttgart', 'Split', 'Geneva', 'Reykjavik'],
        'Stuttgart': ['Porto', 'Split', 'Reykjavik', 'Stockholm'],
        'Oslo': ['Stockholm', 'Split', 'Geneva', 'Porto', 'Tallinn', 'Reykjavik'],
        'Split': ['Stuttgart', 'Oslo', 'Geneva', 'Stockholm'],
        'Geneva': ['Oslo', 'Porto', 'Split', 'Stockholm'],
        'Porto': ['Stuttgart', 'Oslo', 'Geneva'],
        'Tallinn': ['Reykjavik', 'Oslo']
    }
    
    # Required days per city
    req_days = {
        'Oslo': 5,
        'Stuttgart': 5,
        'Reykjavik': 2,
        'Split': 3,
        'Geneva': 2,
        'Porto': 3,
        'Tallinn': 5,
        'Stockholm': 3
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(21)]
    
    s = Solver()
    
    # Each day must be a valid city
    for day in days:
        s.add(Or([day == city_idx[city] for city in cities]))
    
    # Fixed constraints
    s.add(days[0] == city_idx['Reykjavik'])
    s.add(days[1] == city_idx['Reykjavik'])
    s.add(days[18] == city_idx['Porto'])
    s.add(days[19] == city_idx['Porto'])
    s.add(days[20] == city_idx['Porto'])
    
    # Meet friend in Stockholm between days 2-4
    s.add(Or([days[i] == city_idx['Stockholm'] for i in [1, 2, 3]]))
    
    # Flight transitions
    for i in range(20):
        current = days[i]
        next_day = days[i+1]
        s.add(Or(
            current == next_day,
            *[And(current == city_idx[a], next_day == city_idx[b]) 
              for a in flights for b in flights[a]]
        ))
    
    # Count days per city
    for city in cities:
        count = Sum([If(days[i] == city_idx[city], 1, 0) for i in range(21)])
        s.add(count == req_days[city])
    
    # Try to find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(21):
            day = i+1
            city = cities[m.eval(days[i]).as_long()]
            itinerary.append({'day': day, 'place': city})
        
        # Verify flight connections
        valid = True
        for i in range(20):
            current = itinerary[i]['place']
            next_place = itinerary[i+1]['place']
            if current != next_place and next_place not in flights[current]:
                valid = False
                break
        
        if valid:
            return json.dumps({'itinerary': itinerary}, indent=2)
        else:
            return json.dumps({'error': 'Invalid flight connections'}, indent=2)
    else:
        return json.dumps({'error': 'No valid itinerary found'}, indent=2)

print(solve_itinerary())
from z3 import *

def solve_itinerary():
    s = Solver()
    
    # Days are 1 to 7
    days = range(1, 8)
    
    # Cities mapping
    cities = {'Riga': 0, 'Amsterdam': 1, 'Mykonos': 2}
    reverse_map = {0: 'Riga', 1: 'Amsterdam', 2: 'Mykonos'}
    
    # Variables: city at start and end of each day
    city_start = [Int(f'start_{d}') for d in days]
    city_end = [Int(f'end_{d}') for d in days]
    
    # City constraints (0-2)
    for d in days:
        s.add(And(city_start[d-1] >= 0, city_start[d-1] <= 2))
        s.add(And(city_end[d-1] >= 0, city_end[d-1] <= 2))
    
    # Flight constraints (only allowed connections)
    for d in days:
        start = city_start[d-1]
        end = city_end[d-1]
        s.add(Implies(start != end,
                     Or(And(start == cities['Amsterdam'], end == cities['Mykonos']),
                        And(start == cities['Mykonos'], end == cities['Amsterdam']),
                        And(start == cities['Riga'], end == cities['Amsterdam']),
                        And(start == cities['Amsterdam'], end == cities['Riga']))))
    
    # Continuity between days
    for d in range(1, 7):
        s.add(city_end[d-1] == city_start[d])
    
    # Initial conditions (days 1-2 in Riga)
    s.add(city_start[0] == cities['Riga'])
    s.add(city_end[0] == cities['Riga'])
    s.add(city_start[1] == cities['Riga'])
    s.add(city_end[1] == cities['Riga'])
    
    # Count days in each city
    def count_days(city_var):
        return Sum([If(Or(city_start[d-1] == city_var, city_end[d-1] == city_var), 1, 0) for d in days])
    
    s.add(count_days(cities['Riga']) == 2)
    s.add(count_days(cities['Amsterdam']) == 2)
    s.add(count_days(cities['Mykonos']) == 5)
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for d in days:
            start = m.evaluate(city_start[d-1]).as_long()
            end = m.evaluate(city_end[d-1]).as_long()
            if start == end:
                itinerary.append({'day': d, 'place': reverse_map[start]})
            else:
                itinerary.append({'day': d, 'place': f"{reverse_map[start]}/{reverse_map[end]}"})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))
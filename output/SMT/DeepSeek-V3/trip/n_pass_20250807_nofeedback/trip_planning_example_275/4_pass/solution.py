from z3 import *

def solve_itinerary():
    # Define cities and connections
    cities = {
        'Split': 0,
        'Vilnius': 1,
        'Madrid': 2,
        'Santorini': 3
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections (bidirectional)
    connections = [
        (cities['Vilnius'], cities['Split']),
        (cities['Split'], cities['Madrid']),
        (cities['Madrid'], cities['Santorini'])
    ]
    
    s = Solver()
    
    # Decision variables: city each day (1-14)
    days = [Int(f'day_{i}') for i in range(1, 15)]
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Transition constraints
    for i in range(len(days)-1):
        current = days[i]
        next_day = days[i+1]
        # Either stay or move to connected city
        s.add(Or(
            current == next_day,
            *[And(current == a, next_day == b) for a,b in connections],
            *[And(current == b, next_day == a) for a,b in connections]
        ))
    
    # Fixed Santorini days (13-14)
    s.add(days[12] == cities['Santorini'])  # day 13
    s.add(days[13] == cities['Santorini'])  # day 14
    
    # Count days in each city (flight days count for both)
    counts = {
        'Split': Sum([If(d == cities['Split'], 1, 0) for d in days]),
        'Vilnius': Sum([If(d == cities['Vilnius'], 1, 0) for d in days]),
        'Madrid': Sum([If(d == cities['Madrid'], 1, 0) for d in days]),
        'Santorini': Sum([If(d == cities['Santorini'], 1, 0) for d in days])
    }
    
    s.add(counts['Split'] == 5)
    s.add(counts['Vilnius'] == 4)
    s.add(counts['Madrid'] == 6)
    s.add(counts['Santorini'] == 2)
    
    # Additional constraint: Must visit all cities
    for city in cities.values():
        s.add(Or([d == city for d in days]))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, 15):
            city_code = model.evaluate(days[i-1]).as_long()
            itinerary.append({'day': i, 'place': city_names[city_code]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))
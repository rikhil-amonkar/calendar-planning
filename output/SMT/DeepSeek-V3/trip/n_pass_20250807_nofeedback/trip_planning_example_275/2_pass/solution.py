from z3 import *

def solve_itinerary():
    # Define the cities with numeric identifiers
    cities = {
        'Split': 0,
        'Vilnius': 1,
        'Madrid': 2,
        'Santorini': 3
    }
    
    # Inverse mapping for output
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections (undirected)
    connections = [
        (cities['Vilnius'], cities['Split']),
        (cities['Split'], cities['Madrid']),
        (cities['Madrid'], cities['Santorini'])
    ]
    
    # Create a Z3 solver
    s = Solver()
    
    # Variables: city each day (1..14)
    days = [Int(f'day_{i}') for i in range(1, 15)]
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Add transition constraints: consecutive days must be the same or connected
    for i in range(len(days) - 1):
        current = days[i]
        next_day = days[i + 1]
        # Either stay in the same city or move to a connected city
        s.add(Or(
            current == next_day,
            *[And(current == a, next_day == b) for a, b in connections],
            *[And(current == b, next_day == a) for a, b in connections]
        ))
    
    # Santorini must be visited on days 13 and 14
    s.add(days[12] == cities['Santorini'])  # day 13 is index 12 (0-based)
    s.add(days[13] == cities['Santorini'])  # day 14 is index 13
    
    # Total days per city constraints
    split_days = Sum([If(d == cities['Split'], 1, 0) for d in days])
    vilnius_days = Sum([If(d == cities['Vilnius'], 1, 0) for d in days])
    madrid_days = Sum([If(d == cities['Madrid'], 1, 0) for d in days])
    santorini_days = Sum([If(d == cities['Santorini'], 1, 0) for d in days])
    
    s.add(split_days == 5)
    s.add(vilnius_days == 4)
    s.add(madrid_days == 6)
    s.add(santorini_days == 2)  # days 13 and 14
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, 15):
            city_code = model.evaluate(days[i-1]).as_long()
            city_name = city_names[city_code]
            itinerary.append({'day': i, 'place': city_name})
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))
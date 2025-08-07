from z3 import *

def solve_itinerary():
    # Define cities and their codes
    cities = {
        'Split': 0,
        'Vilnius': 1,
        'Madrid': 2,
        'Santorini': 3
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Flight connections (bidirectional)
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
    
    # Track when we're traveling between cities
    traveling = [Bool(f'travel_{i}') for i in range(1, 15)]
    
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
        # Traveling if changing cities
        s.add(traveling[i] == (current != next_day))
    
    # Santorini must be on days 13-14
    s.add(days[12] == cities['Santorini'])  # day 13
    s.add(days[13] == cities['Santorini'])  # day 14
    
    # Count days in each city (including travel days)
    counts = {
        'Split': Sum([If(Or(days[i] == cities['Split'], 
                         And(traveling[i], 
                            Or(days[i] == cities['Split'], 
                               days[i+1] == cities['Split']))), 
                     1, 0) for i in range(14)]),
        'Vilnius': Sum([If(Or(days[i] == cities['Vilnius'], 
                             And(traveling[i], 
                                Or(days[i] == cities['Vilnius'], 
                                   days[i+1] == cities['Vilnius']))), 
                       1, 0) for i in range(14)]),
        'Madrid': Sum([If(Or(days[i] == cities['Madrid'], 
                           And(traveling[i], 
                              Or(days[i] == cities['Madrid'], 
                                 days[i+1] == cities['Madrid']))), 
                     1, 0) for i in range(14)]),
        'Santorini': Sum([If(Or(days[i] == cities['Santorini'], 
                            And(traveling[i], 
                               Or(days[i] == cities['Santorini'], 
                                  days[i+1] == cities['Santorini']))), 
                        1, 0) for i in range(14)])
    }
    
    # Required days in each city
    s.add(counts['Split'] == 5)
    s.add(counts['Vilnius'] == 4)
    s.add(counts['Madrid'] == 6)
    s.add(counts['Santorini'] == 2)
    
    # Must visit all cities at least once
    for city in cities.values():
        s.add(Or([d == city for d in days]))
    
    # Ensure we don't have impossible transitions
    for i in range(len(days)-1):
        current = days[i]
        next_day = days[i+1]
        s.add(Implies(current != next_day, 
                     Or(*[And(current == a, next_day == b) for a,b in connections],
                        *[And(current == b, next_day == a) for a,b in connections])))
    
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
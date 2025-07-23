import json
from z3 import *

def solve_scheduling_problem():
    # Cities and their codes
    cities = {
        'Paris': 0,
        'Warsaw': 1,
        'Krakow': 2,
        'Tallinn': 3,
        'Riga': 4,
        'Copenhagen': 5,
        'Helsinki': 6,
        'Oslo': 7,
        'Santorini': 8,
        'Lyon': 9
    }
    
    # Reverse mapping for city names
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights (undirected)
    direct_flights = [
        (0, 1), (0, 4), (0, 3), (0, 5), (0, 6), (0, 7), (0, 2), (0, 9),
        (1, 4), (1, 3), (1, 5), (1, 6), (1, 7), (1, 2),
        (2, 5), (2, 6), (2, 7),
        (3, 4), (3, 5), (3, 6), (3, 7),
        (4, 5), (4, 6), (4, 7),
        (5, 6), (5, 7), (5, 8),
        (6, 7),
        (7, 8), (7, 9),
        (9, 0)
    ]
    
    # Create flight adjacency list for faster lookups
    flight_graph = {city: set() for city in cities.values()}
    for a, b in direct_flights:
        flight_graph[a].add(b)
        flight_graph[b].add(a)
    
    # Total days
    total_days = 25
    
    # Create Z3 variables for each day (using BitVec for better performance)
    day_vars = [BitVec(f'day_{i}', 4) for i in range(total_days)]
    
    # Solver with optimized parameters
    s = Solver()
    s.set("timeout", 120000)  # 2 minute timeout
    
    # Each day must be a valid city
    for day in day_vars:
        s.add(day >= 0, day <= 9)
    
    # Duration constraints using more efficient encoding
    duration_requirements = [
        (0, 5),  # Paris
        (1, 2),  # Warsaw
        (2, 2),  # Krakow
        (3, 2),  # Tallinn
        (4, 2),  # Riga
        (5, 5),  # Copenhagen
        (6, 5),  # Helsinki
        (7, 5),  # Oslo
        (8, 2),  # Santorini
        (9, 4)   # Lyon
    ]
    
    for city_code, days in duration_requirements:
        s.add(Sum([If(day_vars[i] == city_code, 1, 0) for i in range(total_days)]) == days)
    
    # Event constraints
    event_constraints = [
        (0, 3, 7),    # Paris days 4-8
        (2, 16, 17),   # Krakow days 17-18
        (4, 22, 23),   # Riga days 23-24
        (6, 17, 21),   # Helsinki days 18-22
        (8, 11, 12)    # Santorini days 12-13
    ]
    
    for city_code, start, end in event_constraints:
        s.add(Or([day_vars[i] == city_code for i in range(start, end + 1)]))
    
    # Flight constraints with adjacency list optimization
    for i in range(total_days - 1):
        current = day_vars[i]
        next_day = day_vars[i + 1]
        # Create Or clause for all possible flights from current city
        same_city = current == next_day
        flight_options = []
        for city in cities.values():
            neighbors = flight_graph[city]
            for neighbor in neighbors:
                flight_options.append(And(current == city, next_day == neighbor))
        s.add(Or(same_city, Or(flight_options)))
    
    # Symmetry breaking: force some ordering in the first few days
    s.add(day_vars[0] == 0)  # Start in Paris
    
    # Try to find a solution
    result = s.check()
    if result == sat:
        m = s.model()
        itinerary = []
        for i in range(total_days):
            day = i + 1
            city_code = m.evaluate(day_vars[i]).as_long()
            city = city_names[city_code]
            itinerary.append({'day': day, 'place': city})
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No solution found', 'reason': str(result)}

# Solve and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))
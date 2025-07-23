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
    
    # Create Z3 variables for each day
    day_vars = [Int(f'day_{i}') for i in range(total_days)]
    
    # Solver with optimized parameters
    s = Solver()
    s.set("timeout", 120000)  # 2 minute timeout
    
    # Each day must be a valid city
    for day in day_vars:
        s.add(day >= 0, day <= 9)
    
    # Duration constraints
    duration_constraints = [
        ('Paris', 5),
        ('Warsaw', 2),
        ('Krakow', 2),
        ('Tallinn', 2),
        ('Riga', 2),
        ('Copenhagen', 5),
        ('Helsinki', 5),
        ('Oslo', 5),
        ('Santorini', 2),
        ('Lyon', 4)
    ]
    
    for city, days in duration_constraints:
        s.add(Sum([If(day == cities[city], 1, 0) for day in day_vars]) == days)
    
    # Event constraints
    event_constraints = [
        ('Paris', 3, 7),    # Days 4-8 (0-based: 3-7)
        ('Krakow', 16, 17), # Days 17-18 (0-based: 16-17)
        ('Riga', 22, 23),   # Days 23-24 (0-based: 22-23)
        ('Helsinki', 17, 21), # Days 18-22 (0-based: 17-21)
        ('Santorini', 11, 12) # Days 12-13 (0-based: 11-12)
    ]
    
    for city, start, end in event_constraints:
        s.add(Or([day_vars[i] == cities[city] for i in range(start, end + 1)]))
    
    # Flight constraints with adjacency list optimization
    for i in range(total_days - 1):
        current = day_vars[i]
        next_day = day_vars[i + 1]
        # Create Or clause for all possible flights from current city
        flight_options = []
        for city in cities.values():
            flight_options.append(And(current == city, Or([next_day == neighbor for neighbor in flight_graph[city]])))
        s.add(Or(current == next_day, Or(flight_options)))
    
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
        
        # Verify the solution
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['place']] += 1
        
        for city, days in duration_constraints:
            assert city_days[city] == days
        
        for city, start, end in event_constraints:
            assert any(day_vars[i].as_long() == cities[city] for i in range(start, end + 1))
        
        for i in range(total_days - 1):
            current = itinerary[i]['place']
            next_place = itinerary[i + 1]['place']
            if current != next_place:
                assert (cities[current], cities[next_place]) in direct_flights
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No solution found', 'reason': str(result)}

# Solve and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))
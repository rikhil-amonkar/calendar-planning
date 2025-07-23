from z3 import *

def solve_itinerary():
    # Define cities with unique codes
    cities = {
        'Paris': 0,
        'Vienna': 1,
        'Barcelona': 2,
        'Edinburgh': 3,
        'Krakow': 4,
        'Riga': 5,
        'Hamburg': 6,
        'Stockholm': 7
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections (bidirectional)
    flight_routes = [
        (0, 3), (0, 5), (0, 4), (0, 7), (0, 6), (0, 2), (0, 1),  # Paris connections
        (1, 7), (1, 6), (1, 2), (1, 4), (1, 5),                   # Vienna connections
        (2, 5), (2, 4), (2, 7), (2, 3), (2, 0), (2, 6),           # Barcelona connections
        (3, 0), (3, 7), (3, 5), (3, 4), (3, 2), (3, 6),           # Edinburgh connections
        (4, 2), (4, 7), (4, 0), (4, 3), (4, 1), (4, 5),           # Krakow connections
        (5, 2), (5, 0), (5, 3), (5, 7), (5, 6), (5, 1), (5, 4),   # Riga connections
        (6, 7), (6, 1), (6, 0), (6, 2), (6, 3), (6, 5),           # Hamburg connections
        (7, 6), (7, 1), (7, 0), (7, 2), (7, 3), (7, 4), (7, 5)    # Stockholm connections
    ]
    
    # Create flight graph (dictionary of sets for faster lookup)
    flight_graph = {c: set() for c in cities.values()}
    for a, b in flight_routes:
        flight_graph[a].add(b)
        flight_graph[b].add(a)
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(1, 17)]
    solver = Solver()
    
    # Each day must be one of the cities
    for day in days:
        solver.add(Or([day == c for c in cities.values()]))
    
    # Fixed constraints (must be exactly these cities on these days)
    # Paris wedding days 1-2
    solver.add(days[0] == cities['Paris'])
    solver.add(days[1] == cities['Paris'])
    
    # Hamburg conference days 10-11 (indices 9-10)
    solver.add(days[9] == cities['Hamburg'])
    solver.add(days[10] == cities['Hamburg'])
    
    # Stockholm relatives days 15-16 (indices 14-15)
    solver.add(days[14] == cities['Stockholm'])
    solver.add(days[15] == cities['Stockholm'])
    
    # Edinburgh meet friend between days 12-14 (indices 11-13)
    solver.add(Or([days[i] == cities['Edinburgh'] for i in range(11, 14)]))
    
    # Duration constraints
    required_days = {
        'Paris': 2,
        'Vienna': 4,
        'Barcelona': 2,
        'Edinburgh': 4,
        'Krakow': 3,
        'Riga': 4,
        'Hamburg': 2,
        'Stockholm': 2
    }
    
    for city, name in city_names.items():
        count = Sum([If(d == city, 1, 0) for d in days])
        solver.add(count == required_days[name])
    
    # Flight constraints - consecutive days must be same city or connected by flight
    for i in range(len(days)-1):
        current = days[i]
        next_day = days[i+1]
        solver.add(Or(
            current == next_day,
            *[And(current == a, next_day == b) for a, b in flight_routes]
        ))
    
    # Try to solve
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(1, 17):
            city_code = model.evaluate(days[i-1]).as_long()
            itinerary.append({'day': i, 'place': city_names[city_code]})
        
        # Verify all constraints are met
        def verify_solution(itinerary):
            # Check fixed days
            if itinerary[0]['place'] != 'Paris' or itinerary[1]['place'] != 'Paris':
                return False
            if itinerary[9]['place'] != 'Hamburg' or itinerary[10]['place'] != 'Hamburg':
                return False
            if itinerary[14]['place'] != 'Stockholm' or itinerary[15]['place'] != 'Stockholm':
                return False
            if not any(itinerary[i]['place'] == 'Edinburgh' for i in range(11,14)):
                return False
            
            # Check day counts
            counts = {city: 0 for city in cities}
            for day in itinerary:
                counts[day['place']] += 1
            for city, req in required_days.items():
                if counts[city] != req:
                    return False
            
            # Check flight connections
            for i in range(len(itinerary)-1):
                current = cities[itinerary[i]['place']]
                next_c = cities[itinerary[i+1]['place']]
                if current != next_c and next_c not in flight_graph[current]:
                    return False
            
            return True
        
        if verify_solution(itinerary):
            return {'itinerary': itinerary}
        else:
            return {'error': 'Solution found but failed verification'}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))
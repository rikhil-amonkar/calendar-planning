import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Oslo', 'Stuttgart', 'Reykjavik', 'Split', 'Geneva', 'Porto', 'Tallinn', 'Stockholm']
    
    # Direct flights as adjacency list
    direct_flights = {
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
    required_days = {
        'Oslo': 5,
        'Stuttgart': 5,
        'Reykjavik': 2,
        'Split': 3,
        'Geneva': 2,
        'Porto': 3,
        'Tallinn': 5,
        'Stockholm': 3
    }
    
    # Create Z3 variables for each day (1..21)
    days = [Int(f'day_{i}') for i in range(1, 22)]
    
    # Create a solver instance
    solver = Solver()
    
    # Each day must be one of the cities (represented by their index)
    city_indices = {city: idx for idx, city in enumerate(cities)}
    for day in days:
        solver.add(Or([day == city_indices[city] for city in cities]))
    
    # Fixed constraints:
    # Days 1-2 in Reykjavik
    solver.add(days[0] == city_indices['Reykjavik'])
    solver.add(days[1] == city_indices['Reykjavik'])
    
    # Days 19-21 in Porto (indices 18-20 in zero-based)
    solver.add(days[18] == city_indices['Porto'])
    solver.add(days[19] == city_indices['Porto'])
    solver.add(days[20] == city_indices['Porto'])
    
    # Meet friend in Stockholm between day 2 and day 4 (indices 1-3 in zero-based)
    solver.add(Or([days[i] == city_indices['Stockholm'] for i in [1, 2, 3]]))
    
    # Flight transitions: consecutive days must be same city or connected by direct flight
    for i in range(len(days) - 1):
        current_city = days[i]
        next_city = days[i + 1]
        solver.add(Or(
            current_city == next_city,
            *[
                And(current_city == city_indices[city_a], next_city == city_indices[city_b])
                for city_a in cities
                for city_b in direct_flights.get(city_a, [])
            ]
        ))
    
    # Count days per city and ensure they match required days
    for city in cities:
        count = Sum([If(day == city_indices[city], 1, 0) for day in days])
        solver.add(count == required_days[city])
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(1, 22):
            day_var = days[i - 1]
            city_idx = model.eval(day_var).as_long()
            city = cities[city_idx]
            itinerary.append({'day': i, 'place': city})
        
        # Convert to JSON
        result = {'itinerary': itinerary}
        return json.dumps(result, indent=2)
    else:
        return json.dumps({'error': 'No valid itinerary found'}, indent=2)

# Execute the solver and print the result
print(solve_itinerary())
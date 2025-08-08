import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Stockholm': 3,
        'Hamburg': 5,
        'Florence': 2,
        'Istanbul': 5,
        'Oslo': 5,
        'Vilnius': 5,
        'Santorini': 2,
        'Munich': 5,
        'Frankfurt': 4,
        'Krakow': 5
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ('Oslo', 'Stockholm'),
        ('Krakow', 'Frankfurt'),
        ('Krakow', 'Istanbul'),
        ('Munich', 'Stockholm'),
        ('Hamburg', 'Stockholm'),
        ('Krakow', 'Vilnius'),
        ('Oslo', 'Istanbul'),
        ('Istanbul', 'Stockholm'),
        ('Oslo', 'Krakow'),
        ('Vilnius', 'Istanbul'),
        ('Oslo', 'Vilnius'),
        ('Frankfurt', 'Istanbul'),
        ('Oslo', 'Frankfurt'),
        ('Munich', 'Hamburg'),
        ('Munich', 'Istanbul'),
        ('Oslo', 'Munich'),
        ('Frankfurt', 'Florence'),
        ('Oslo', 'Hamburg'),
        ('Vilnius', 'Frankfurt'),
        ('Florence', 'Munich'),
        ('Krakow', 'Munich'),
        ('Hamburg', 'Istanbul'),
        ('Frankfurt', 'Stockholm'),
        ('Stockholm', 'Santorini'),
        ('Frankfurt', 'Munich'),
        ('Santorini', 'Oslo'),
        ('Krakow', 'Stockholm'),
        ('Vilnius', 'Munich'),
        ('Frankfurt', 'Hamburg')
    ]
    
    # Correct city names in direct_flights
    corrected_flights = []
    for a, b in direct_flights:
        a_corrected = a
        b_corrected = b
        if a == 'Hamburg':
            a_corrected = 'Hamburg'
        if b == 'Hamburg':
            b_corrected = 'Hamburg'
        if a == 'Munich':
            a_corrected = 'Munich'
        if b == 'Munich':
            b_corrected = 'Munich'
        if a == 'Florence':
            a_corrected = 'Florence'
        if b == 'Florence':
            b_corrected = 'Florence'
        corrected_flights.append((a_corrected, b_corrected))
    
    # Unique list of cities
    all_cities = list(cities.keys())
    
    # Create a mapping from city to index
    city_index = {city: idx for idx, city in enumerate(all_cities)}
    
    # Number of days
    num_days = 32
    
    # Z3 variables: for each day, which city are you in?
    day_city = [Int(f'day_{day}_city') for day in range(num_days)]
    
    # Solver
    solver = Solver()
    
    # Each day_city must be between 0 and len(all_cities) - 1
    for day in range(num_days):
        solver.add(day_city[day] >= 0, day_city[day] < len(all_cities))
    
    # Precompute flight connections for quick lookup
    flight_connections = {}
    for a, b in corrected_flights:
        if a not in flight_connections:
            flight_connections[a] = set()
        if b not in flight_connections:
            flight_connections[b] = set()
        flight_connections[a].add(b)
        flight_connections[b].add(a)
    
    # Constraints for transitions: consecutive days must be either same city or have a direct flight
    for day in range(num_days - 1):
        current_city_var = day_city[day]
        next_city_var = day_city[day + 1]
        # Either stay in the same city or move to a connected city
        same_city = current_city_var == next_city_var
        connected_cities = []
        for city in all_cities:
            if city in flight_connections:
                for connected_city in flight_connections[city]:
                    connected_cities.append(And(current_city_var == city_index[city], next_city_var == city_index[connected_city]))
        solver.add(Or(same_city, *connected_cities))
    
    # Constraints for the number of days in each city
    for city, req_days in cities.items():
        idx = city_index[city]
        solver.add(Sum([If(day_city[day] == idx, 1, 0) for day in range(num_days)]) == req_days)
    
    # Fixed constraints:
    # Istanbul from day 25 to 29 (inclusive, 1-based)
    istanbul_idx = city_index['Istanbul']
    for day in range(24, 29):  # 0-based: days 24-28 (1-based 25-29)
        solver.add(day_city[day] == istanbul_idx)
    
    # Krakow workshop between day 5 and 9 (1-based days 5-9)
    krakow_idx = city_index['Krakow']
    for day in range(4, 9):  # 0-based days 4-8 (1-based 5-9)
        solver.add(day_city[day] == krakow_idx)
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for day in range(num_days):
            city_idx = model.evaluate(day_city[day]).as_long()
            itinerary.append({
                'day': day + 1,
                'city': all_cities[city_idx]
            })
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))
from z3 import *

def solve_scheduling_problem():
    # Define cities and days
    cities = ['Helsinki', 'Warsaw', 'Madrid', 'Split', 'Reykjavik', 'Budapest']
    n_days = 14
    days = range(1, n_days + 1)
    
    # Create Z3 variables for each day
    day_vars = [Int(f'day_{i}') for i in days]
    
    # Create solver with optimization
    s = Solver()
    s.set("timeout", 60000)  # Increase timeout to 60 seconds
    
    # Map cities to integers
    city_map = {city: idx for idx, city in enumerate(cities)}
    city_inv_map = {idx: city for idx, city in enumerate(cities)}
    
    # Each day must be assigned to a valid city
    for day in day_vars:
        s.add(Or([day == city_map[city] for city in cities]))
    
    # Define direct flight connections (bidirectional)
    direct_flights = [
        ('Helsinki', 'Reykjavik'),
        ('Budapest', 'Warsaw'),
        ('Madrid', 'Split'),
        ('Helsinki', 'Split'),
        ('Helsinki', 'Madrid'),
        ('Helsinki', 'Budapest'),
        ('Reykjavik', 'Warsaw'),
        ('Helsinki', 'Warsaw'),
        ('Madrid', 'Budapest'),
        ('Budapest', 'Reykjavik'),
        ('Madrid', 'Warsaw'),
        ('Warsaw', 'Split'),
        ('Reykjavik', 'Madrid')
    ]
    
    # Convert flight connections to city indices
    flight_connections = []
    for a, b in direct_flights:
        flight_connections.append((city_map[a], city_map[b]))
        flight_connections.append((city_map[b], city_map[a]))  # Bidirectional
    
    # Flight constraints between consecutive days
    for i in range(n_days - 1):
        current = day_vars[i]
        next_day = day_vars[i + 1]
        s.add(Or(
            current == next_day,  # Stay in same city
            Or([And(current == a, next_day == b) for a, b in flight_connections])
        ))
    
    # Duration constraints for each city
    duration = {
        'Helsinki': 2,
        'Warsaw': 3,
        'Madrid': 4,
        'Split': 4,
        'Reykjavik': 2,
        'Budapest': 4
    }
    
    for city, total in duration.items():
        city_idx = city_map[city]
        count = Sum([If(day_vars[i] == city_idx, 1, 0) for i in range(n_days)])
        s.add(count == total)
    
    # Fixed day constraints
    # Helsinki on days 1 and 2
    s.add(day_vars[0] == city_map['Helsinki'])
    s.add(day_vars[1] == city_map['Helsinki'])
    
    # Reykjavik on day 8 or 9
    s.add(Or(
        day_vars[7] == city_map['Reykjavik'],
        day_vars[8] == city_map['Reykjavik']
    ))
    
    # Warsaw on days 9, 10, or 11
    s.add(Or(
        day_vars[8] == city_map['Warsaw'],
        day_vars[9] == city_map['Warsaw'],
        day_vars[10] == city_map['Warsaw']
    ))
    
    # Additional constraints to help the solver
    # No immediate return to same city unless staying
    for i in range(n_days - 2):
        s.add(Implies(
            day_vars[i] != day_vars[i + 1],
            day_vars[i + 1] != day_vars[i + 2]
        ))
    
    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(n_days):
            city_idx = model.evaluate(day_vars[day]).as_long()
            itinerary.append({'day': day + 1, 'place': city_inv_map[city_idx]})
        
        return {'itinerary': itinerary}
    else:
        return None

# Solve and print the result
solution = solve_scheduling_problem()
if solution:
    print(solution)
else:
    print("No solution found.")
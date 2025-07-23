from z3 import *

def solve_scheduling_problem():
    # Define the cities
    cities = ['Helsinki', 'Warsaw', 'Madrid', 'Split', 'Reykjavik', 'Budapest']
    n_days = 14
    days = range(1, n_days + 1)
    
    # Create Z3 variables: day_1, day_2, ..., day_14 each can be one of the cities
    day_vars = [Int(f'day_{i}') for i in days]
    
    # Create a solver instance
    s = Solver()
    
    # Map each city to an integer
    city_map = {city: idx for idx, city in enumerate(cities)}
    city_inv_map = {idx: city for idx, city in enumerate(cities)}
    
    # Constraints: each day_var must be one of the city indices
    for day in day_vars:
        s.add(Or([day == city_map[city] for city in cities]))
    
    # Direct flight connections as tuples of city indices
    direct_flights = [
        (city_map['Helsinki'], city_map['Reykjavik']),
        (city_map['Budapest'], city_map['Warsaw']),
        (city_map['Madrid'], city_map['Split']),
        (city_map['Helsinki'], city_map['Split']),
        (city_map['Helsinki'], city_map['Madrid']),
        (city_map['Helsinki'], city_map['Budapest']),
        (city_map['Reykjavik'], city_map['Warsaw']),
        (city_map['Helsinki'], city_map['Warsaw']),
        (city_map['Madrid'], city_map['Budapest']),
        (city_map['Budapest'], city_map['Reykjavik']),
        (city_map['Madrid'], city_map['Warsaw']),
        (city_map['Warsaw'], city_map['Split']),
        (city_map['Reykjavik'], city_map['Madrid']),
    ]
    # Ensure flights are bidirectional
    bidirectional_flights = direct_flights.copy()
    for (a, b) in direct_flights:
        bidirectional_flights.append((b, a))
    direct_flights = bidirectional_flights
    
    # Flight constraints: consecutive days must be either same city or connected by a direct flight
    for i in range(n_days - 1):
        current_day = day_vars[i]
        next_day = day_vars[i + 1]
        s.add(Or(
            current_day == next_day,
            Or([And(current_day == a, next_day == b) for (a, b) in direct_flights])
        ))
    
    # Duration constraints
    for city in cities:
        city_idx = city_map[city]
        if city == 'Helsinki':
            total_days = 2
        elif city == 'Warsaw':
            total_days = 3
        elif city == 'Madrid':
            total_days = 4
        elif city == 'Split':
            total_days = 4
        elif city == 'Reykjavik':
            total_days = 2
        elif city == 'Budapest':
            total_days = 4
        # Count the number of days assigned to this city
        count = Sum([If(day_vars[i] == city_idx, 1, 0) for i in range(n_days)])
        s.add(count == total_days)
    
    # Fixed day constraints
    # Helsinki on days 1 and 2 (workshop between day 1 and 2)
    s.add(day_vars[0] == city_map['Helsinki'])
    s.add(day_vars[1] == city_map['Helsinki'])
    
    # Reykjavik between day 8 and 9 (i.e., day 8 or day 9 is Reykjavik)
    s.add(Or(
        day_vars[7] == city_map['Reykjavik'],  # day 8
        day_vars[8] == city_map['Reykjavik']   # day 9
    ))
    
    # Warsaw between day 9 and 11 (i.e., days 9, 10, or 11)
    s.add(Or(
        day_vars[8] == city_map['Warsaw'],  # day 9
        day_vars[9] == city_map['Warsaw'],  # day 10
        day_vars[10] == city_map['Warsaw']   # day 11
    ))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(n_days):
            city_idx = model.evaluate(day_vars[day]).as_long()
            itinerary.append({'day': day + 1, 'place': city_inv_map[city_idx]})
        
        # Verify the solution meets all constraints
        # (This is a sanity check; Z3 should have ensured it)
        # Convert to JSON-like structure
        result = {
            'itinerary': itinerary
        }
        return result
    else:
        return None

# Solve the problem and print the result
solution = solve_scheduling_problem()
if solution:
    print(solution)
else:
    print("No solution found.")
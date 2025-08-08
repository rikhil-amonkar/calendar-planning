from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Naples', 'Valencia', 'Stuttgart', 'Split', 'Venice', 'Amsterdam', 'Nice', 'Barcelona', 'Porto']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: list of tuples (city1, city2)
    direct_flights = [
        ('Venice', 'Nice'), ('Naples', 'Amsterdam'), ('Barcelona', 'Nice'),
        ('Amsterdam', 'Nice'), ('Stuttgart', 'Valencia'), ('Stuttgart', 'Porto'),
        ('Split', 'Stuttgart'), ('Split', 'Naples'), ('Valencia', 'Amsterdam'),
        ('Barcelona', 'Porto'), ('Valencia', 'Naples'), ('Venice', 'Amsterdam'),
        ('Barcelona', 'Naples'), ('Barcelona', 'Valencia'), ('Split', 'Amsterdam'),
        ('Barcelona', 'Venice'), ('Stuttgart', 'Amsterdam'), ('Naples', 'Nice'),
        ('Venice', 'Stuttgart'), ('Split', 'Barcelona'), ('Porto', 'Nice'),
        ('Barcelona', 'Stuttgart'), ('Venice', 'Naples'), ('Porto', 'Amsterdam'),
        ('Porto', 'Valencia'), ('Stuttgart', 'Naples'), ('Barcelona', 'Amsterdam')
    ]
    
    # Convert flight connections into a set of tuples for easy lookup
    flight_connections = set()
    for a, b in direct_flights:
        flight_connections.add((a, b))
        flight_connections.add((b, a))
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # Variables: for each day (1..24), which city is visited (represented by index)
    day_city = [Int(f'day_{day}_city') for day in range(1, 25)]
    
    # Each day's city must be one of the 9 cities (0..8)
    for day in range(24):
        solver.add(day_city[day] >= 0, day_city[day] < 9)
    
    # Flight constraints: consecutive days must be either the same city or connected by a direct flight
    for day in range(23):
        current_city = day_city[day]
        next_city = day_city[day + 1]
        # Either stay in the same city or move to a connected city
        same_city = current_city == next_city
        move_constraints = []
        for a, b in flight_connections:
            a_idx = city_indices[a]
            b_idx = city_indices[b]
            move_constraints.append(And(current_city == a_idx, next_city == b_idx))
        solver.add(Or(same_city, Or(move_constraints)))
    
    # Duration constraints for each city
    required_days = {
        'Naples': 3,
        'Valencia': 5,
        'Stuttgart': 2,
        'Split': 5,
        'Venice': 5,
        'Amsterdam': 4,
        'Nice': 2,
        'Barcelona': 2,
        'Porto': 4
    }
    
    for city, req_days in required_days.items():
        city_idx = city_indices[city]
        # Count the number of days spent in this city
        total_days = Sum([If(day_city[day] == city_idx, 1, 0) for day in range(24)])
        solver.add(total_days == req_days)
    
    # Specific constraints:
    # 1. Spend 3 days in Naples. Meet friend in Naples between day 18-20: at least one day in Naples in 18-20.
    naples_idx = city_indices['Naples']
    solver.add(Or(
        day_city[17] == naples_idx,  # day 18 (0-based: 17)
        day_city[18] == naples_idx,
        day_city[19] == naples_idx
    ))
    
    # 2. Valencia: 5 days
    # 3. Stuttgart: 2 days
    # 4. Split: 5 days
    # 5. Venice: 5 days, conference between day 6-10 (must be in Venice during days 5-9 in 0-based)
    venice_idx = city_indices['Venice']
    for day in [5, 6, 7, 8, 9]:  # days 6-10 (1-based)
        solver.add(day_city[day] == venice_idx)
    
    # 6. Amsterdam: 4 days
    # 7. Nice: 2 days, meet friends between day 23-24 (days 22-23 0-based)
    nice_idx = city_indices['Nice']
    solver.add(Or(
        day_city[22] == nice_idx,
        day_city[23] == nice_idx
    ))
    
    # 8. Barcelona: 2 days, workshop between day 5-6 (days 4-5 0-based)
    barcelona_idx = city_indices['Barcelona']
    solver.add(Or(
        day_city[4] == barcelona_idx,
        day_city[5] == barcelona_idx
    ))
    
    # 9. Porto: 4 days
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        city_names = cities
        for day in range(24):
            city_idx = model.evaluate(day_city[day]).as_long()
            itinerary.append({
                'day': day + 1,
                'place': city_names[city_idx]
            })
        
        # Verify the solution meets all constraints
        # (This is a sanity check; the solver should ensure it)
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Generate the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))
from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Manchester', 'Stuttgart', 'Madrid', 'Vienna']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    idx_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Vienna': ['Stuttgart', 'Manchester', 'Madrid'],
        'Stuttgart': ['Vienna', 'Manchester'],
        'Manchester': ['Vienna', 'Stuttgart', 'Madrid'],
        'Madrid': ['Vienna', 'Manchester']
    }
    
    # Total days
    total_days = 15
    
    # Create Z3 variables for each day: day 1 to day 15
    day_vars = [Int(f'day_{i}') for i in range(1, total_days + 1)]
    
    s = Solver()
    
    # Each day variable must be between 0 and 3 (city indices)
    for day in day_vars:
        s.add(day >= 0, day < len(cities))
    
    # Manchester must be from day 1 to day 7 (wedding)
    for i in range(1, 8):  # days 1-7 (1-based)
        s.add(day_vars[i-1] == city_to_idx['Manchester'])
    
    # Stuttgart must be visited between day 11-15 (workshop)
    # At least one day in Stuttgart in days 11-15
    stuttgart_in_workshop_days = Or([day_vars[i-1] == city_to_idx['Stuttgart'] for i in range(11, 16)])
    s.add(stuttgart_in_workshop_days)
    
    # Total days per city
    # Manchester: 7 days (already days 1-7)
    # So additional Manchester days can be 0
    # But total Manchester days must be 7. So no additional days beyond 1-7.
    # So sum of Manchester days is 7.
    manchester_days = Sum([If(day_vars[i] == city_to_idx['Manchester'], 1, 0) for i in range(total_days)])
    s.add(manchester_days == 7)
    
    # Stuttgart: 5 days
    stuttgart_days = Sum([If(day_vars[i] == city_to_idx['Stuttgart'], 1, 0) for i in range(total_days)])
    s.add(stuttgart_days == 5)
    
    # Madrid: 4 days
    madrid_days = Sum([If(day_vars[i] == city_to_idx['Madrid'], 1, 0) for i in range(total_days)])
    s.add(madrid_days == 4)
    
    # Vienna: 2 days
    vienna_days = Sum([If(day_vars[i] == city_to_idx['Vienna'], 1, 0) for i in range(total_days)])
    s.add(vienna_days == 2)
    
    # Flight constraints: consecutive days can only be the same city or connected by direct flight
    for i in range(total_days - 1):
        current_city_idx = day_vars[i]
        next_city_idx = day_vars[i+1]
        current_city = idx_to_city[current_city_idx.as_long() if is_const(current_city_idx) else current_city_idx]
        next_city = idx_to_city[next_city_idx.as_long() if is_const(next_city_idx) else next_city_idx]
        
        # Either same city or direct flight
        s.add(Or(
            current_city_idx == next_city_idx,
            And(
                current_city_idx != next_city_idx,
                Or([next_city in direct_flights[current_city] for current_city in cities for next_city in cities if current_city != next_city])
            )
        ))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, total_days + 1):
            day_var = day_vars[i-1]
            city_idx = model[day_var].as_long()
            city = idx_to_city[city_idx]
            itinerary.append({'day': i, 'place': city})
        
        # Verify the solution meets all constraints
        # (This is a sanity check; Z3 should ensure it)
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    print(result)
else:
    print("No valid itinerary found.")
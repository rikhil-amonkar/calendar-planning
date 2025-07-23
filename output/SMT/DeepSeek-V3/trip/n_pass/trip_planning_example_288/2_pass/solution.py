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
    for i in range(7):  # days 1-7 (0-based index)
        s.add(day_vars[i] == city_to_idx['Manchester'])
    
    # Stuttgart must be visited between day 11-15 (workshop)
    # At least one day in Stuttgart in days 11-15
    stuttgart_in_workshop_days = Or([day_vars[i] == city_to_idx['Stuttgart'] for i in range(10, 15)])
    s.add(stuttgart_in_workshop_days)
    
    # Total days per city
    # Manchester: 7 days (already days 1-7)
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
        current_city = day_vars[i]
        next_city = day_vars[i + 1]
        s.add(Or(
            current_city == next_city,
            And(
                current_city != next_city,
                Or([And(current_city == city_to_idx[city], next_city == city_to_idx[adj]) 
                    for city in cities 
                    for adj in direct_flights[city]])
            )
        ))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(total_days):
            city_idx = model.eval(day_vars[i]).as_long()
            city = idx_to_city[city_idx]
            itinerary.append({'day': i + 1, 'place': city})
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    print(result)
else:
    print("No valid itinerary found.")
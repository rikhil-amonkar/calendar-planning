from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Krakow', 'Frankfurt', 'Oslo', 'Dubrovnik', 'Naples']
    n_cities = len(cities)
    city_to_idx = {city: i for i, city in enumerate(cities)}
    
    # Direct flights adjacency matrix
    direct_flights = [
        [False, True, True, False, False],   # Krakow
        [True, False, True, True, True],     # Frankfurt
        [True, True, False, True, True],     # Oslo
        [False, True, True, False, True],    # Dubrovnik
        [False, True, True, True, False]    # Naples
    ]
    
    total_days = 18
    days = list(range(total_days))  # 0-based for days 1-18
    
    # Z3 variables: city each day (end of the day)
    city_vars = [Int(f'city_{d}') for d in days]
    for d in days:
        set_option(max_args=10000000)
    
    solver = Solver()
    
    # Constraint: city_vars[d] must be a valid city index
    for d in days:
        solver.add(city_vars[d] >= 0, city_vars[d] < n_cities)
    
    # 1. Total days per city
    # For a city C, the total days is:
    # - The number of days d where city_vars[d] == C (end of day d+1 is C)
    # Plus the number of days d where city_vars[d-1] == C and city_vars[d] != C (flying out of C on day d+1)
    # But day 0's previous city is not applicable. So perhaps the initial city is city_vars[0], and day 1 is city_vars[0] and city_vars[1], etc.
    # Alternatively, the total days in C is the number of days where either:
    # - city_vars[d] == C, or
    # - (d > 0 and city_vars[d-1] == C and city_vars[d] != C)
    
    def days_in_city(city_idx):
        total = 0
        for d in days:
            # Current day is part of the city if:
            # - end of day is city_idx, or
            # - flying out on this day (i.e., previous end was city_idx and current is not)
            current_in_city = If(city_vars[d] == city_idx, 1, 0)
            if d > 0:
                fly_out = If(And(city_vars[d-1] == city_idx, city_vars[d] != city_idx), 1, 0)
            else:
                fly_out = 0
            total += current_in_city + fly_out
        return total
    
    # Constraints for each city's total days
    solver.add(days_in_city(city_to_idx['Krakow']) == 5)
    solver.add(days_in_city(city_to_idx['Frankfurt']) == 4)
    solver.add(days_in_city(city_to_idx['Oslo']) == 3)
    solver.add(days_in_city(city_to_idx['Dubrovnik']) == 5)
    solver.add(days_in_city(city_to_idx['Naples']) == 5)
    
    # 2. Specific date constraints
    # Oslo must be visited on days 16-18 (1-based) which are days 15-17 0-based in city_vars
    for d in [15, 16, 17]:
        solver.add(city_vars[d] == city_to_idx['Oslo'])
    
    # Dubrovnik must be visited at least once between days 5-9 (1-based) which are days 4-8 0-based
    solver.add(Or([city_vars[d] == city_to_idx['Dubrovnik'] for d in range(4, 9)]))
    
    # 3. Flight transitions: if city changes between d-1 and d, there must be a direct flight
    for d in range(1, total_days):
        c_prev = city_vars[d-1]
        c_current = city_vars[d]
        for c1 in range(n_cities):
            for c2 in range(n_cities):
                if c1 != c2:
                    solver.add(Implies(
                        And(c_prev == c1, c_current == c2),
                        direct_flights[c1][c2]
                    ))
    
    # Solve
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for d in days:
            city_idx = model.evaluate(city_vars[d]).as_long()
            itinerary.append({'day': d+1, 'place': cities[city_idx]})
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
print(json.dumps(result, indent=2))
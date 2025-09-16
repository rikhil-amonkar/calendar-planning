from z3 import *

def solve_itinerary():
    s = Solver()
    n_days = 16
    cities = ["Barcelona", "Oslo", "Brussels", "Stuttgart", "Split", "Copenhagen", "Venice"]
    n_cities = len(cities)
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # City for each day
    city_vars = [Int(f"city_{d}") for d in range(1, n_days+1)]
    for d in range(n_days):
        s.add(city_vars[d] >= 0, city_vars[d] < n_cities)
    
    # Start in Barcelona and end in Venice
    s.add(city_vars[0] == city_to_int["Barcelona"])
    s.add(city_vars[15] == city_to_int["Venice"])
    
    # Travel only on days 4, 8, 12 (index 3,7,11)
    for d in range(1, n_days):
        if d+1 not in [4,8,12]:
            s.add(city_vars[d] == city_vars[d-1])
    
    # Each city is visited
    visited = [Int(f"visited_{i}") for i in range(n_cities)]
    for i in range(n_cities):
        s.add(visited[i] == If(Or([city_vars[d] == i for d in range(n_days)]), 1, 0))
    s.add(Sum(visited) == n_cities)
    
    # Consecutive days per city and exactly one city has 1-day stay
    min_days = [Int(f"min_days_{i}") for i in range(n_cities)]
    one_day_stay = Int("one_day_stay")
    one_day_stay_city = Int("one_day_stay_city")
    for i in range(n_cities):
        first_day = Int(f"first_day_{i}")
        last_day = Int(f"last_day_{i}")
        s.add(first_day >= 0, first_day < n_days)
        s.add(last_day >= 0, last_day < n_days)
        
        in_city_days = [If(city_vars[d] == i, 1, 0) for d in range(n_days)]
        s.add(Or(Sum(in_city_days) == 0, Sum(in_city_days) >= 2), Or(Sum(in_city_days) == 0, Sum(in_city_days) == 1, Sum(in_city_days) >= 2))
        
        s.add(Implies(Sum(in_city_days) > 0, first_day == Min([If(city_vars[d] == i, d, n_days) for d in range(n_days)]))
        s.add(Implies(Sum(in_city_days) > 0, last_day == Max([If(city_vars[d] == i, d, -1) for d in range(n_days)]))
        s.add(Implies(Sum(in_city_days) > 0, last_day - first_day + 1 == Sum(in_city_days)))
        
        min_days[i] = Sum(in_city_days)
        s.add(Implies(min_days[i] > 0, min_days[i] >= 2))
    
    one_day_possible = [If(min_days[i] == 1, 1, 0) for i in range(n_cities)]
    s.add(Sum(one_day_possible) == 1)
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_city = model.eval(city_vars[0]).as_long()
        start_day = 1
        for d in range(1, n_days):
            curr_city_val = model.eval(city_vars[d]).as_long()
            prev_city_val = model.eval(city_vars[d-1]).as_long()
            if curr_city_val != prev_city_val:
                end_day = d
                itinerary.append({
                    'day_range': f"Day {start_day}-{end_day}",
                    'place': int_to_city[prev_city_val]
                })
                start_day = d+1
        itinerary.append({
            'day_range': f"Day {start_day}-{n_days}",
            'place': int_to_city[model.eval(city_vars[n_days-1]).as_long()]
        })
        return {'itinerary': itinerary}
    else:
        return "No solution found"

result = solve_itinerary()
print(result)
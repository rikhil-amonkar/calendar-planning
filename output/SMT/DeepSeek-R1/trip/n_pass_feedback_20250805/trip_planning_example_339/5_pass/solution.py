from z3 import Solver, Int, If, sat

def plan_trip():
    cities = ['Warsaw', 'Budapest', 'Paris', 'Riga']
    min_days = [2, 4, 3, 3]
    total_days = 17
    num_cities = len(cities)
    
    # Decision variables
    order = [Int(f'order_{i}') for i in range(num_cities)]
    start = [Int(f'start_{i}') for i in range(num_cities)]
    duration = [Int(f'duration_{i}') for i in range(num_cities)]
    
    s = Solver()
    
    # Order must be a permutation of city indices
    s.add([And(o >= 0, o < num_cities) for o in order])
    s.add(Distinct(order))
    
    # First city starts on day 1
    s.add(start[0] == 1)
    
    # Consecutive cities: next starts after previous duration
    for i in range(num_cities - 1):
        s.add(start[i+1] == start[i] + duration[i])
    
    # Last city ends on total_days
    s.add(start[-1] + duration[-1] - 1 == total_days)
    
    # Duration constraints per city based on order
    for i in range(num_cities):
        min_req = If(order[i] == 0, min_days[0],
                  If(order[i] == 1, min_days[1],
                  If(order[i] == 2, min_days[2], min_days[3])))
        s.add(duration[i] >= min_req)
        s.add(duration[i] <= total_days)  # Upper bound for efficiency
        
    # Solve and format itinerary
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(num_cities):
            city_idx = m.evaluate(order[i]).as_long()
            s_val = m.evaluate(start[i]).as_long()
            d_val = m.evaluate(duration[i]).as_long()
            end_val = s_val + d_val - 1
            day_range = f"Day {s_val}-{end_val}"
            itinerary.append({'day_range': day_range, 'place': cities[city_idx]})
        return {'itinerary': itinerary}
    else:
        return None

result = plan_trip()
if result:
    print(result)
else:
    print("No valid plan found")
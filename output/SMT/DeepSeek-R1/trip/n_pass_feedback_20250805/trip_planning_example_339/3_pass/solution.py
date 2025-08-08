from z3 import Solver, Int, sat

def plan_trip():
    cities = ['Warsaw', 'Budapest', 'Paris', 'Riga']
    min_days = [2, 4, 3, 3]
    total_days = 17
    num_cities = len(cities)
    
    starts = [Int(f'start_{i}') for i in range(num_cities)]
    ends = [Int(f'end_{i}') for i in range(num_cities)]
    
    s = Solver()
    
    # First city starts on Day 1
    s.add(starts[0] == 1)
    # Last city ends on Day 17
    s.add(ends[-1] == total_days)
    
    # End of each city equals start of next city
    for i in range(num_cities - 1):
        s.add(ends[i] == starts[i+1])
    
    # Minimum stay constraints
    for i in range(num_cities):
        duration = ends[i] - starts[i] + 1
        s.add(duration >= min_days[i])
        s.add(duration <= total_days)  # Upper bound for efficiency
    
    # All days must be between 1 and 17
    for i in range(num_cities):
        s.add(starts[i] >= 1, starts[i] <= total_days)
        s.add(ends[i] >= 1, ends[i] <= total_days)
    
    # Solve and format itinerary
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(num_cities):
            start_val = m.eval(starts[i]).as_long()
            end_val = m.eval(ends[i]).as_long()
            day_range = f"Day {start_val}-{end_val}"
            itinerary.append({'day_range': day_range, 'place': cities[i]})
        return {'itinerary': itinerary}
    else:
        return None

result = plan_trip()
if result:
    print(result)
else:
    print("No valid plan found")
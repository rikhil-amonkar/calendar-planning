from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Days are 1 to 10
    days = 10
    # Cities: 0=Krakow, 1=Dubrovnik, 2=Frankfurt
    cities = ['Krakow', 'Dubrovnik', 'Frankfurt']
    
    # Variables for each day: starting city (s) and ending city (e)
    s_vars = [Int('s_%d' % i) for i in range(1, days+1)]
    e_vars = [Int('e_%d' % i) for i in range(1, days+1)]
    
    # Constraint: Each day's start and end must be valid cities (0,1,2)
    for i in range(days):
        s.add(s_vars[i] >= 0, s_vars[i] <= 2)
        s.add(e_vars[i] >= 0, e_vars[i] <= 2)
    
    # Constraint: Next day's start equals previous day's end
    for i in range(days-1):
        s.add(s_vars[i+1] == e_vars[i])
    
    # Direct flights constraint: Only allowed transitions
    allowed_pairs = [(0,2), (2,0), (1,2), (2,1)]
    for i in range(days):
        s.add(If(s_vars[i] != e_vars[i],
                 Or([And(s_vars[i] == a, e_vars[i] == b) for (a,b) in allowed_pairs]),
                 True))
    
    # Wedding constraint: Must be in Krakow on day 9 and day 10
    s.add(Or(s_vars[8] == 0, e_vars[8] == 0))  # Day 9
    s.add(Or(s_vars[9] == 0, e_vars[9] == 0))  # Day 10
    
    # Total days constraints
    total_k = Sum([If(Or(s_vars[i] == 0, e_vars[i] == 0), 1, 0) for i in range(days)])
    total_d = Sum([If(Or(s_vars[i] == 1, e_vars[i] == 1), 1, 0) for i in range(days)])
    total_f = Sum([If(Or(s_vars[i] == 2, e_vars[i] == 2), 1, 0) for i in range(days)])
    s.add(total_k == 2)
    s.add(total_d == 7)
    s.add(total_f == 3)
    
    # Check satisfaction
    if s.check() == sat:
        m = s.model()
        # Get values for each day
        s_vals = [m.evaluate(s_vars[i]).as_long() for i in range(days)]
        e_vals = [m.evaluate(e_vars[i]).as_long() for i in range(days)]
        
        # Generate itinerary segments
        segments = []
        current_city = s_vals[0]
        start_day = 1
        for i in range(days):
            if i < days-1 and e_vals[i] != s_vals[i+1]:
                # Travel day: segment ends current day
                segments.append((start_day, i+1, current_city))
                current_city = s_vals[i+1]
                start_day = i+1
        segments.append((start_day, days, current_city))
        
        # Format output
        itinerary = []
        for seg in segments:
            start, end, city_idx = seg
            city_name = cities[city_idx]
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city_name})
        
        # Output as JSON
        import json
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()
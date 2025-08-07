from z3 import *
import json

def main():
    CityNames = ["Nice", "Dublin", "Krakow", "Lyon", "Frankfurt"]
    req_by_index = [5, 7, 6, 4, 2]
    
    adj = [
        [0, 1, 0, 1, 1],
        [1, 0, 1, 1, 1],
        [0, 1, 0, 0, 1],
        [1, 1, 0, 0, 1],
        [1, 1, 1, 1, 0]
    ]
    
    # Create Z3 variables
    s = [Int(f's_{i}') for i in range(5)]  # Start days for segments
    c = [Int(f'c_{i}') for i in range(5)]   # City assignments for segments
    
    solver = Solver()
    
    # Each city assigned to exactly one segment
    solver.add(Distinct(c))
    
    # Cities must be in valid range
    for i in range(5):
        solver.add(c[i] >= 0, c[i] <= 4)
    
    # Segment start day constraints
    # Nice must start on day 1 (only possible start given 5-day requirement)
    solver.add(Or([And(c[i] == 0, s[i] == 1) for i in range(5)]))
    
    # Frankfurt must start on day 18 or 19
    solver.add(Or([And(c[i] == 4, Or(s[i] == 18, s[i] == 19)) for i in range(5)]))
    
    # Length expressions for each segment based on city
    L = []
    for i in range(5):
        L_i = Int(f'L_{i}')
        solver.add(L_i == If(c[i] == 0, req_by_index[0],
                             If(c[i] == 1, req_by_index[1],
                                If(c[i] == 2, req_by_index[2],
                                   If(c[i] == 3, req_by_index[3], 
                                      req_by_index[4])))))
        L.append(L_i)
    
    # Segment end day constraints
    for i in range(5):
        solver.add(s[i] + L[i] - 1 <= 20)
        solver.add(s[i] >= 1)
    
    # Non-overlapping constraints
    for i in range(5):
        for j in range(i+1, 5):
            solver.add(Or(
                s[i] + L[i] <= s[j],  # Segment i ends before j starts
                s[j] + L[j] <= s[i]   # Segment j ends before i starts
            ))
    
    # Consecutive segment travel constraints
    # For each pair of segments, if they are consecutive in time, enforce travel constraint
    for i in range(5):
        for j in range(5):
            if i == j:
                continue
            # Check if segment j starts immediately after segment i
            consecutive = And(s[j] == s[i] + L[i])
            
            # Get city indices
            city_i = c[i]
            city_j = c[j]
            
            # Create adjacency constraint
            adj_allowed = Or(
                And(city_i == 0, Or(city_j == 1, city_j == 3, city_j == 4)),
                And(city_i == 1, Or(city_j == 0, city_j == 2, city_j == 3, city_j == 4)),
                And(city_i == 2, Or(city_j == 1, city_j == 4)),
                And(city_i == 3, Or(city_j == 0, city_j == 1, city_j == 4)),
                And(city_i == 4, Or(city_j == 0, city_j == 1, city_j == 2, city_j == 3))
            )
            
            # If segments are consecutive in time, enforce travel constraint
            solver.add(Implies(consecutive, adj_allowed))
    
    # Total days must be covered (not strictly necessary but helps constraint propagation)
    solver.add(Sum([If(And(s[i] <= day, day <= s[i] + L[i] - 1), 1, 0) 
                  for i in range(5) for day in range(1, 21)]) == 20)
    
    # Check and get solution
    if solver.check() == sat:
        m = solver.model()
        s_val = [m.eval(s_i).as_long() for s_i in s]
        c_val = [m.eval(c_i).as_long() for c_i in c]
        L_val = [m.eval(L_i).as_long() for L_i in L]
        
        # Build daily itinerary
        itinerary = []
        for day in range(1, 21):
            for i in range(5):
                start = s_val[i]
                end = start + L_val[i] - 1
                if start <= day <= end:
                    itinerary.append({"day": day, "place": CityNames[c_val[i]]})
                    break
        
        # Validate we have exactly 20 days
        if len(itinerary) != 20:
            print('{"itinerary": []}')
        else:
            print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()
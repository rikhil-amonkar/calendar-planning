from z3 import *

def main():
    # Given input data
    cities = ['New York', 'Los Angeles', 'Chicago', 'Houston']
    durations = [3, 5, 2, 4]
    travel = [
        [0, 5, 3, 4],
        [5, 0, 2, 3],
        [3, 2, 0, 2],
        [4, 3, 2, 0]
    ]
    
    n = len(cities)
    solver = Solver()
    
    # Order of visit: list of n Z3 IntVars, each in [0, n-1]
    order = [Int('order_%d' % i) for i in range(n)]
    # Start times for the cities in the order they are visited
    t = [Int('t_%d' % i) for i in range(n)]
    # Start times for each city by original index
    start_times = [Int('start_%d' % i) for i in range(n)]
    
    # Constraints: order is a permutation of [0, n-1]
    solver.add(Distinct(order))
    for i in range(n):
        solver.add(order[i] >= 0, order[i] < n)
    
    # First city starts at day 1
    solver.add(t[0] == 1)
    
    # For each segment from k to k+1
    for k in range(n-1):
        d_k = Int('d_%d' % k)       # Duration of the city at position k
        tr_k = Int('tr_%d' % k)     # Travel time from city at position k to next city
        
        # Constraint: d_k equals the duration of the city at order[k]
        d_conds = []
        for i in range(n):
            d_conds.append(And(order[k] == i, d_k == durations[i]))
        solver.add(Or(d_conds))
        
        # Constraint: tr_k equals travel[order[k]][order[k+1]]
        tr_conds = []
        for i in range(n):
            for j in range(n):
                tr_conds.append(And(order[k] == i, order[k+1] == j, tr_k == travel[i][j]))
        solver.add(Or(tr_conds))
        
        # Next start time = current start time + duration + travel time
        solver.add(t[k+1] == t[k] + d_k + tr_k)
    
    # Constraint: start_times[i] is the start time of the city with index i
    for i in range(n):
        s_conds = []
        for k in range(n):
            s_conds.append(And(order[k] == i, start_times[i] == t[k]))
        solver.add(Or(s_conds))
    
    # Constraint: entire trip ends by day 365
    last_duration = Int('last_duration')
    last_conds = []
    for i in range(n):
        last_conds.append(And(order[n-1] == i, last_duration == durations[i]))
    solver.add(Or(last_conds))
    solver.add(t[n-1] + last_duration <= 365)
    
    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        # Extract the order of cities
        visit_order = []
        for k in range(n):
            idx = model.evaluate(order[k]).as_long()
            visit_order.append(cities[idx])
        
        # Extract start times for each city by original index
        city_start_times = {}
        for i in range(n):
            start_val = model.evaluate(start_times[i]).as_long()
            city_start_times[cities[i]] = start_val
        
        # Output the solution
        print("Order:", visit_order)
        print("Start times:")
        for city in cities:
            print(f"  {city}: {city_start_times[city]}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()
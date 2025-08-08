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
    
    # Constraints: order is a permutation of [0, n-1]
    solver.add(Distinct(order))
    for i in range(n):
        solver.add(order[i] >= 0, order[i] < n)
    
    # First city starts at day 1
    solver.add(t[0] == 1)
    
    # Duration function mapping city index to its duration
    dur_func = Function('dur_func', IntSort(), IntSort())
    for i in range(n):
        solver.add(dur_func(i) == durations[i])
    
    # Travel time function mapping (from_city, to_city) to travel time
    travel_func = Function('travel_func', IntSort(), IntSort(), IntSort())
    for i in range(n):
        for j in range(n):
            solver.add(travel_func(i, j) == travel[i][j])
    
    # For each segment from k to k+1
    for k in range(n - 1):
        # Get duration of current city and travel time to next city
        d_k = dur_func(order[k])
        tr_k = travel_func(order[k], order[k+1])
        # Next start time = current start time + duration + travel time
        solver.add(t[k+1] == t[k] + d_k + tr_k)
    
    # Start time function mapping city index to its start time
    start_func = Function('start_func', IntSort(), IntSort())
    for k in range(n):
        solver.add(start_func(order[k]) == t[k])
    
    # Entire trip must end by day 365
    last_duration = dur_func(order[n-1])
    solver.add(t[n-1] + last_duration <= 365)
    
    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        # Extract the order of cities
        visit_order = []
        for k in range(n):
            idx = model.evaluate(order[k]).as_long()
            visit_order.append(cities[idx])
        
        # Extract start times for each city
        city_start_times = {}
        for i, city in enumerate(cities):
            start_val = model.evaluate(start_func(i)).as_long()
            city_start_times[city] = start_val
        
        # Output the solution
        print("Order:", visit_order)
        print("Start times:")
        for city in cities:
            print(f"  {city}: {city_start_times[city]}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()
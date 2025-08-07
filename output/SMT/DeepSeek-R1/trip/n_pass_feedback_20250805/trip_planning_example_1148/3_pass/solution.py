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
    
    # Create arrays for durations and travel times
    dur_array = Array('dur_array', IntSort(), IntSort())
    for i in range(n):
        solver.add(dur_array[i] == durations[i])
    
    travel_array = Array('travel_array', IntSort(), IntSort())
    for i in range(n):
        for j in range(n):
            solver.add(travel_array[i * n + j] == travel[i][j])
    
    # For each segment from k to k+1
    for k in range(n - 1):
        # Get duration of current city and travel time to next
        d_k = dur_array[order[k]]
        tr_k = travel_array[order[k] * n + order[k + 1]]
        # Next start time = current start time + duration + travel time
        solver.add(t[k + 1] == t[k] + d_k + tr_k)
    
    # Create array for start times of each city by index
    start_array = Array('start_array', IntSort(), IntSort())
    for k in range(n):
        solver.add(start_array[order[k]] == t[k])
    
    # Entire trip must end by day 365
    last_duration = dur_array[order[n - 1]]
    solver.add(t[n - 1] + last_duration <= 365)
    
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
            start_val = model.evaluate(start_array[i]).as_long()
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
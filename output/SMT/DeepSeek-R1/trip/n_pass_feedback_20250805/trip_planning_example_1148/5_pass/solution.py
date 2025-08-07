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
    
    # Order of visit: permutation of city indices
    order = [Int('order_%d' % i) for i in range(n)]
    # Start times for cities in visit order
    t = [Int('t_%d' % i) for i in range(n)]
    
    # Constraints: order is a permutation of [0, n-1]
    solver.add(Distinct(order))
    for i in range(n):
        solver.add(order[i] >= 0, order[i] < n)
    
    # First city starts at day 1
    solver.add(t[0] == 1)
    
    # Create durations array
    dur_array = Array('dur_array', IntSort(), IntSort())
    for i in range(n):
        dur_array = Store(dur_array, i, durations[i])
    
    # Create travel array (1D flattened)
    travel_array = Array('travel_array', IntSort(), IntSort())
    for i in range(n):
        for j in range(n):
            travel_array = Store(travel_array, i * n + j, travel[i][j])
    
    # For each segment in the trip
    for k in range(n - 1):
        # Get current and next city indices from order
        current_city = order[k]
        next_city = order[k+1]
        
        # Get duration of current city
        d_k = Select(dur_array, current_city)
        # Get travel time from current to next city
        tr_k = Select(travel_array, current_city * n + next_city)
        
        # Next start time = current start + duration + travel
        solver.add(t[k+1] == t[k] + d_k + tr_k)
    
    # Create array for start times per city
    start_array = Array('start_array', IntSort(), IntSort())
    for k in range(n):
        city_index = order[k]
        start_array = Store(start_array, city_index, t[k])
    
    # Entire trip must end by day 365
    last_city = order[n-1]
    last_duration = Select(dur_array, last_city)
    solver.add(t[n-1] + last_duration <= 365)
    
    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        # Extract visit order
        visit_order = []
        for k in range(n):
            idx = model.evaluate(order[k]).as_long()
            visit_order.append(cities[idx])
        
        # Extract start times for each city
        city_start_times = {}
        for i, city in enumerate(cities):
            start_val = model.evaluate(Select(start_array, i)).as_long()
            city_start_times[city] = start_val
        
        # Output solution
        print("Order:", visit_order)
        print("Start times:")
        for city in cities:
            print(f"  {city}: {city_start_times[city]}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()
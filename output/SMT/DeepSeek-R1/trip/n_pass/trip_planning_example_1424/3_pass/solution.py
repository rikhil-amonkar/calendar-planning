from z3 import *

def main():
    # Cities and their connections with distances
    cities = ["Seattle", "Denver", "Chicago", "Boston", "New York", "San Francisco"]
    distances = [
        [0, 1300, 2000, 3000, 2800, 800],    # Seattle
        [1300, 0, 1000, 1800, 1600, 1500],   # Denver
        [2000, 1000, 0, 1000, 800, 2200],    # Chicago
        [3000, 1800, 1000, 0, 400, 3100],    # Boston
        [2800, 1600, 800, 400, 0, 2900],     # New York
        [800, 1500, 2200, 3100, 2900, 0]     # San Francisco
    ]
    
    # Trip parameters
    start_city = "Seattle"
    end_city = "New York"
    pass_cities = ["Chicago", "Denver"]
    max_total_distance = 6000

    # Find city indices with case-insensitive matching
    start_city_idx = next(i for i, c in enumerate(cities) if c.lower() == start_city.lower())
    end_city_idx = next(i for i, c in enumerate(cities) if c.lower() == end_city.lower())
    pass_city_idxs = [cities.index(c) for c in pass_cities]

    n = len(cities)
    
    # Create Z3 variables
    L = Int('L')  # Path length (number of cities visited)
    step = [Int(f'step_{i}') for i in range(n)]  # City index at each step
    total_distance = Int('total_distance')
    
    # Create solver
    solver = Solver()
    
    # Path length constraints (at least 2, at most n cities)
    solver.add(L >= 2, L <= n)
    
    # Start and end constraints
    solver.add(step[0] == start_city_idx)
    solver.add(step[L-1] == end_city_idx)
    
    # All visited cities must be valid indices
    for i in range(n):
        solver.add(If(i < L, 
                     And(step[i] >= 0, step[i] < n), 
                     True))  # Steps beyond path length unconstrained
    
    # Cities in path must be distinct
    solver.add(Distinct([step[i] for i in range(L)]))
    
    # Define distance function
    dist_func = Function('dist', IntSort(), IntSort(), IntSort())
    for i in range(n):
        for j in range(n):
            solver.add(dist_func(i, j) == distances[i][j])
    
    # Calculate total distance
    distance_terms = []
    for i in range(n-1):
        # Distance between consecutive cities in path
        dist_val = If(And(i < L-1, step[i] != step[i+1]),
                     dist_func(step[i], step[i+1]),
                     0)
        distance_terms.append(dist_val)
    
    solver.add(total_distance == Sum(distance_terms))
    solver.add(total_distance <= max_total_distance)
    
    # Must visit all pass cities
    for cidx in pass_city_idxs:
        solver.add(Or([step[i] == cidx for i in range(L)]))
    
    # Try to solve
    if solver.check() == sat:
        model = solver.model()
        path_length = model.eval(L).as_long()
        
        # Extract route
        route_idxs = [model.eval(step[i]).as_long() for i in range(path_length)]
        route_names = [cities[idx] for idx in route_idxs]
        
        # Calculate actual distance for verification
        actual_distance = 0
        for i in range(path_length-1):
            actual_distance += distances[route_idxs[i]][route_idxs[i+1]]
        
        # Verify required cities
        required_cities = set([start_city, end_city] + pass_cities)
        covered_cities = set(route_names)
        
        # Print results
        print(f"Route: {' -> '.join(route_names)}")
        print(f"Total distance: {actual_distance} miles")
        print(f"Required places: {sorted(required_cities)}")
        print(f"Covered required places: {covered_cities >= required_cities}")
    else:
        print("No valid route found")

if __name__ == "__main__":
    main()
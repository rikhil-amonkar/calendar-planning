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
    start_city = "Seattle"  # Intentionally misspelled to test error handling
    end_city = "New York"
    pass_cities = ["Chicago", "Denver"]
    max_total_distance = 6000

    # Find city indices with case-insensitive matching
    start_city_idx = next((i for i, c in enumerate(cities) if c.lower() == start_city.lower()), None)
    end_city_idx = next((i for i, c in enumerate(cities) if c.lower() == end_city.lower()), None)
    
    # Validate city names
    if start_city_idx is None:
        print(f"Error: Start city '{start_city}' not found in city list.")
        print(f"Available cities: {', '.join(cities)}")
        return
    if end_city_idx is None:
        print(f"Error: End city '{end_city}' not found in city list.")
        print(f"Available cities: {', '.join(cities)}")
        return

    n = len(cities)
    
    # Create Z3 variables
    next_city_var = [Int(f"next_{i}") for i in range(n)]
    total_distance = Int("total_distance")
    visited = [Bool(f"visited_{i}") for i in range(n)]

    # Create solver
    solver = Solver()

    # Constraint: next_city_var must be valid city indices
    for i in range(n):
        solver.add(Or(*[next_city_var[i] == j for j in range(n)]))

    # Constraint: no self-loops
    for i in range(n):
        solver.add(next_city_var[i] != i)

    # Constraint: start city is first in path
    solver.add(next_city_var[start_city_idx] != end_city_idx)

    # Constraint: path must be contiguous
    for i in range(n):
        if i != end_city_idx:
            solver.add(Or(*[next_city_var[j] == i for j in range(n) if j != i]))

    # Constraint: total distance calculation
    solver.add(total_distance == Sum([
        If(And(i != end_city_idx, next_city_var[i] == j), 
           distances[i][j], 0) 
        for i in range(n) for j in range(n)
    ]))
    solver.add(total_distance <= max_total_distance)

    # Constraint: must visit pass_cities
    for city in pass_cities:
        idx = cities.index(city)
        solver.add(Or(*[next_city_var[i] == idx for i in range(n) if i != idx]))

    # Constraint: define visited cities
    for i in range(n):
        solver.add(visited[i] == Or(
            next_city_var[i] != end_city_idx,  # Not last city
            Or(*[next_city_var[j] == i for j in range(n)])  # Visited as next of some city
        ))

    # Try to solve
    if solver.check() == sat:
        model = solver.model()
        # Extract route
        route = []
        current = start_city_idx
        while current != end_city_idx:
            route.append(current)
            current = model.eval(next_city_var[current]).as_long()
        route.append(end_city_idx)
        
        # Convert to city names
        route_names = [cities[i] for i in route]
        
        # Verify required cities coverage
        required_cities = set(pass_cities) | {cities[start_city_idx], cities[end_city_idx]}
        covered_cities = set(route_names)
        
        # Print results
        print(f"Route: {' -> '.join(route_names)}")
        print(f"Total distance: {model.eval(total_distance).as_long()} miles")
        print(f"Required places: {sorted(required_cities)}")
        print(f"Covered required places: {covered_cities >= required_cities}")
    else:
        print("No valid route found")

if __name__ == "__main__":
    main()
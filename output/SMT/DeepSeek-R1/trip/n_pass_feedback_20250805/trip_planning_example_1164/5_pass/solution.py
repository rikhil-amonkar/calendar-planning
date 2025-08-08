from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Problem parameters
    n_days = 3
    n_cities = 3
    required_stays = [1, 1, 1]  # Each city must be visited exactly once
    
    # Adjacency matrix (0: not connected, 1: connected)
    adj = [
        [0, 1, 0],
        [1, 0, 1],
        [0, 1, 0]
    ]
    
    # Precompute allowed city transitions
    allowed_transitions = []
    for i in range(n_cities):
        for j in range(n_cities):
            if adj[i][j] == 1:
                allowed_transitions.append((i, j))
    
    # Create Z3 variables for city each day
    cities = [Int(f'day_{i}_city') for i in range(n_days)]
    
    # Create stay duration variables for each city
    stays = [Int(f'stay_city_{i}') for i in range(n_cities)]
    
    # Constraint: Cities must be valid (0-2)
    for city_var in cities:
        s.add(city_var >= 0, city_var < n_cities)
    
    # Constraint: Start at city 0, end at city 2
    s.add(cities[0] == 0)
    s.add(cities[n_days-1] == 2)
    
    # Constraint: Valid transitions between consecutive days
    for i in range(n_days - 1):
        s.add(Or([
            And(cities[i] == start, cities[i+1] == end)
            for (start, end) in allowed_transitions
        ]))
    
    # Constraint: Calculate stay durations
    for city_idx in range(n_cities):
        s.add(stays[city_idx] == Sum([
            If(cities[day] == city_idx, 1, 0) 
            for day in range(n_days)
        ]))
    
    # Constraint: Meet stay requirements
    for city_idx in range(n_cities):
        s.add(stays[city_idx] == required_stays[city_idx])
    
    # Solve and output results
    if s.check() == sat:
        model = s.model()
        print("Valid solution found:")
        for day in range(n_days):
            city = model[cities[day]].as_long()
            print(f"Day {day}: City {city}")
        print("\nStay durations:")
        for city_idx in range(n_cities):
            duration = model[stays[city_idx]].as_long()
            print(f"City {city_idx}: {duration} day(s)")
    else:
        print("No valid solution found")

if __name__ == "__main__":
    main()
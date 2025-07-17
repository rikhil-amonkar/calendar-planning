from z3 import *

def main():
    # Example data
    n_days = 3
    cities = ['New York', 'London', 'Tokyo']
    start_city = 'New York'
    end_city = 'Tokyo'
    flight_matrix = {
        'New York': {'London': True, 'Tokyo': False},
        'London': {'New York': True, 'Tokyo': True},
        'Tokyo': {'New York': False, 'London': False}
    }
    
    # Build flight_matrix_index: a 2D list of booleans, n x n
    n = len(cities)
    flight_matrix_index = [[False] * n for _ in range(n)]
    for i, city1 in enumerate(cities):
        if city1 in flight_matrix:
            for j, city2 in enumerate(cities):
                if city2 in flight_matrix[city1]:
                    flight_matrix_index[i][j] = flight_matrix[city1][city2]
    
    # Create Z3 solver and variables
    s = Solver()
    assignment = [Int(f"day_{i}") for i in range(n_days)]
    
    # Constraint: each assignment must be between 0 and n-1
    for a in assignment:
        s.add(a >= 0, a < n)
    
    # Start and end constraints
    start_idx = cities.index(start_city)
    s.add(assignment[0] == start_idx)
    end_idx = cities.index(end_city)
    s.add(assignment[-1] == end_idx)
    
    # Visit each city at least once
    for idx in range(n):
        s.add(Or([assignment[i] == idx for i in range(n_days)]))
    
    # Flight constraints between consecutive days
    for i in range(1, n_days):
        prev_city_idx = assignment[i - 1]
        current_city_idx = assignment[i]
        allowed_pairs = []
        for idx1 in range(n):
            for idx2 in range(n):
                if flight_matrix_index[idx1][idx2]:
                    allowed_pairs.append(And(prev_city_idx == idx1, current_city_idx == idx2))
        s.add(Or(allowed_pairs))
    
    # Solve and print solution
    if s.check() == sat:
        m = s.model()
        plan = []
        for i in range(n_days):
            city_idx = m.evaluate(assignment[i]).as_long()
            plan.append(cities[city_idx])
        print("Travel Plan:")
        for day, city in enumerate(plan):
            print(f"Day {day + 1}: {city}")
    else:
        print("No valid travel plan found.")

if __name__ == "__main__":
    main()
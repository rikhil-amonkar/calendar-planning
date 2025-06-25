from z3 import *

def main():
    import sys
    data = sys.stdin.read().splitlines()
    if not data:
        print("No valid travel plan found.")
        return
    
    n_days, n_cities = map(int, data[0].split())
    cities = []
    index = 1
    for _ in range(n_cities):
        cities.append(data[index].strip())
        index += 1
        
    start_city = data[index].strip()
    index += 1
    end_city = data[index].strip()
    index += 1
    
    flight_matrix_index = []
    for _ in range(n_cities):
        row = list(map(int, data[index].split()))
        flight_matrix_index.append([x == 1 for x in row])
        index += 1

    if n_cities > n_days:
        print("No valid travel plan found.")
        return

    s = Solver()
    s.set("timeout", 9000)  # Set timeout to 9 seconds (9000ms)
    
    # Use BitVec instead of Int for better performance
    assignment = [BitVec(f"day_{i}", 8) for i in range(n_days)]
    
    # Constraint: each assignment must be between 0 and n_cities-1
    for a in assignment:
        s.add(ULT(a, n_cities))
    
    start_idx = cities.index(start_city)
    s.add(assignment[0] == start_idx)
    end_idx = cities.index(end_city)
    s.add(assignment[-1] == end_idx)
    
    # Visit each city at least once
    for city_idx in range(n_cities):
        s.add(Or([assignment[i] == city_idx for i in range(n_days)]))
    
    # Define a flight function for efficient constraints
    Flight = Function('Flight', BitVecSort(8), BitVecSort(8), BoolSort())
    
    # Set flight function values
    for i in range(n_cities):
        for j in range(n_cities):
            s.add(Flight(i, j) == flight_matrix_index[i][j])
    
    # Add flight constraints between consecutive days
    for i in range(1, n_days):
        s.add(Flight(assignment[i-1], assignment[i]))
    
    # Check for solution
    result = s.check()
    if result == sat:
        m = s.model()
        plan = []
        for i in range(n_days):
            city_idx = m.evaluate(assignment[i]).as_long()
            plan.append(cities[city_idx])
        print("Travel Plan:")
        for day, city in enumerate(plan):
            print(f"Day {day + 1}: {city}")
    elif result == unknown:
        print("No valid travel plan found (timeout).")
    else:
        print("No valid travel plan found.")

if __name__ == "__main__":
    main()
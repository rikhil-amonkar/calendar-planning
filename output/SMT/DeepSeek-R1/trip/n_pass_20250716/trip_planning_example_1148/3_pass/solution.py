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
    assignment = [Int(f"day_{i}") for i in range(n_days)]
    
    for a in assignment:
        s.add(a >= 0, a < n_cities)
    
    start_idx = cities.index(start_city)
    s.add(assignment[0] == start_idx)
    end_idx = cities.index(end_city)
    s.add(assignment[-1] == end_idx)
    
    for city_idx in range(n_cities):
        s.add(Or([assignment[i] == city_idx for i in range(n_days)]))
    
    for i in range(1, n_days):
        prev_city_idx = assignment[i-1]
        curr_city_idx = assignment[i]
        allowed_pairs = []
        for idx1 in range(n_cities):
            for idx2 in range(n_cities):
                if flight_matrix_index[idx1][idx2]:
                    allowed_pairs.append(And(prev_city_idx == idx1, curr_city_idx == idx2))
        s.add(Or(allowed_pairs))
    
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
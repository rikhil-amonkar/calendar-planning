from z3 import *

def main():
    n_days = 13
    cities = ['Madrid', 'Seville', 'Porto', 'Stuttgart']
    n_cities = len(cities)
    direct_pairs = [(0, 1), (0, 2), (1, 2), (2, 3)]
    
    start_city = [Int(f'start_city_{i}') for i in range(n_days)]
    travel = [Bool(f'travel_{i}') for i in range(n_days)]
    dest_city = [Int(f'dest_city_{i}') for i in range(n_days)]
    
    s = Solver()
    
    for i in range(n_days):
        s.add(start_city[i] >= 0, start_city[i] < n_cities)
        s.add(dest_city[i] >= 0, dest_city[i] < n_cities)
    
    s.add(start_city[0] == 0)
    
    fixed_travel = [False, False, False, True, True, False, True] + [False] * 6
    for i in range(n_days):
        s.add(travel[i] == fixed_travel[i])
    
    for i in range(1, n_days):
        s.add(start_city[i] == If(travel[i-1], dest_city[i-1], start_city[i-1]))
    
    for i in range(4):
        s.add(If(travel[i], Or(start_city[i] == 0, dest_city[i] == 0), start_city[i] == 0))
    
    for i in range(4, n_days):
        s.add(If(travel[i], And(start_city[i] != 0, dest_city[i] != 0), start_city[i] != 0))
    
    for i in [6, 12]:
        s.add(If(travel[i], Or(start_city[i] == 3, dest_city[i] == 3), start_city[i] == 3))
    
    total_days = [0] * n_cities
    for c in range(n_cities):
        total = 0
        for i in range(n_days):
            in_city = If(travel[i], Or(start_city[i] == c, dest_city[i] == c), start_city[i] == c)
            total += If(in_city, 1, 0)
        s.add(total == [4, 2, 3, 7][c])
    
    for i in range(n_days):
        if fixed_travel[i]:
            constraints = []
            for a, b in direct_pairs:
                constraints.append(And(start_city[i] == a, dest_city[i] == b))
                constraints.append(And(start_city[i] == b, dest_city[i] == a))
            s.add(Or(constraints))
    
    if s.check() == sat:
        m = s.model()
        start_vals = [m.evaluate(start_city[i]).as_long() for i in range(n_days)]
        travel_vals = [m.evaluate(travel[i]) for i in range(n_days)]
        dest_vals = [m.evaluate(dest_city[i]).as_long() for i in range(n_days)]
        
        for i in range(n_days):
            if is_true(travel_vals[i]):
                print(f"Day {i+1}: {[cities[start_vals[i]], cities[dest_vals[i]]]}")
            else:
                print(f"Day {i+1}: {[cities[start_vals[i]]]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
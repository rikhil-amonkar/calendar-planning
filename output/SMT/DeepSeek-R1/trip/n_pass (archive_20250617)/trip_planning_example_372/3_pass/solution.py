from z3 import *

def main():
    n_days = 13
    cities = ['Madrid', 'Seville', 'Porto', 'Stuttgart']
    n_cities = len(cities)
    direct_pairs = [(0,1), (0,2), (1,2), (2,3)]
    allowed_pairs = set()
    for a, b in direct_pairs:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))
    
    s = [Int(f's_{i}') for i in range(n_days)]
    d = [Int(f'd_{i}') for i in range(n_days)]
    travel = [Bool(f'travel_{i}') for i in range(n_days)]
    
    s_solver = Solver()
    
    for i in range(n_days):
        s_solver.add(s[i] >= 0, s[i] < n_cities)
        s_solver.add(d[i] >= 0, d[i] < n_cities)
    
    s_solver.add(s[0] == 0)
    
    for i in range(4):
        s_solver.add(s[i] == 0)
    
    s_solver.add(s[6] == 3)
    s_solver.add(s[12] == 3)
    
    for i in [0, 1, 2, 6, 12]:
        s_solver.add(travel[i] == False)
    
    for i in range(n_days):
        s_solver.add(If(travel[i], s[i] != d[i], s[i] == d[i]))
    
    for i in range(1, n_days):
        s_solver.add(s[i] == d[i-1])
    
    for i in range(n_days):
        if i not in [0, 1, 2, 6, 12]:
            constraints = []
            for a, b in allowed_pairs:
                constraints.append(And(s[i] == a, d[i] == b))
            s_solver.add(If(travel[i], Or(constraints), True))
    
    total_travel = Sum([If(travel[i], 1, 0) for i in range(n_days)])
    s_solver.add(total_travel == 3)
    
    for c in range(n_cities):
        total = 0
        for i in range(n_days):
            total += If(Or(s[i] == c, d[i] == c), 1, 0)
        s_solver.add(total == [4, 2, 3, 7][c])
    
    if s_solver.check() == sat:
        m = s_solver.model()
        start_vals = [m.evaluate(s[i]).as_long() for i in range(n_days)]
        travel_vals = [m.evaluate(travel[i]) for i in range(n_days)]
        dest_vals = [m.evaluate(d[i]).as_long() for i in range(n_days)]
        
        for i in range(n_days):
            if is_true(travel_vals[i]):
                print(f"Day {i+1}: {[cities[start_vals[i]], cities[dest_vals[i]]]}")
            else:
                print(f"Day {i+1}: {[cities[start_vals[i]]]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
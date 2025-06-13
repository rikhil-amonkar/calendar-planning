from z3 import *

def main():
    cities = ["Krakow", "Frankfurt", "Oslo", "Dubrovnik", "Naples"]
    allowed_pairs = [(0, 1), (0, 2), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]
    allowed_edges = []
    for a, b in allowed_pairs:
        allowed_edges.append((a, b))
        allowed_edges.append((b, a))
    
    required_days = [5, 4, 3, 5, 5]
    
    s = [Int('s%d' % i) for i in range(1, 20)]
    solver = Solver()
    
    for i in range(19):
        solver.add(s[i] >= 0, s[i] <= 4)
    
    for i in range(18):
        edge_constraint = Or([And(s[i] == a, s[i+1] == b) for (a, b) in allowed_edges])
        solver.add(If(s[i] != s[i+1], edge_constraint, True))
    
    for c in range(5):
        total = 0
        for i in range(18):
            total += If(Or(s[i] == c, s[i+1] == c), 1, 0)
        solver.add(total == required_days[c])
    
    oslo_full_days = []
    for i in range(15, 18):
        oslo_full_days.append(And(s[i] == 2, s[i+1] == 2))
    solver.add(Or(oslo_full_days))
    
    dubrovnik_full_days = []
    for i in range(4, 9):
        dubrovnik_full_days.append(And(s[i] == 3, s[i+1] == 3))
    solver.add(Or(dubrovnik_full_days))
    
    previous_solution = [4, 4, 4, 4, 4, 3, 3, 3, 3, 1, 1, 1, 0, 0, 0, 0, 2, 2, 2]
    block = Or(*[s[i] != previous_solution[i] for i in range(19)])
    solver.add(block)
    
    if solver.check() == sat:
        model = solver.model()
        s_vals = [model.evaluate(s[i]).as_long() for i in range(19)]
        
        for day in range(1, 19):
            idx = day - 1
            start_city = s_vals[idx]
            end_city = s_vals[idx+1]
            if start_city == end_city:
                print(f"Day {day}: Stay in {cities[start_city]}")
            else:
                print(f"Day {day}: Travel from {cities[start_city]} to {cities[end_city]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
from z3 import *

def main():
    cities = ["Krakow", "Frankfurt", "Oslo", "Dubrovnik", "Naples"]
    allowed_pairs = [(0, 1), (0, 2), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]
    allowed_edges = []
    for a, b in allowed_pairs:
        allowed_edges.append((a, b))
        allowed_edges.append((b, a))
    
    required_days = [5, 4, 3, 5, 5]
    
    s = [Int('s%d' % i) for i in range(19)]
    solver = Solver()
    
    # Start in Naples, end in Krakow
    solver.add(s[0] == 4)
    solver.add(s[18] == 0)
    
    for i in range(19):
        solver.add(s[i] >= 0, s[i] <= 4)
    
    for i in range(18):
        edge_constraint = Or([And(s[i] == a, s[i+1] == b) for (a, b) in allowed_edges])
        solver.add(If(s[i] != s[i+1], edge_constraint, True))
    
    # Day count constraint: days = nights 0-17
    for c in range(5):
        total = 0
        for i in range(18):
            total += If(s[i] == c, 1, 0)
        solver.add(total == required_days[c])
    
    # Oslo full day constraint (days 16-18)
    oslo_full_days = []
    for day in [16, 17, 18]:
        # Full day requires same city on previous and current night
        oslo_full_days.append(And(s[day-1] == 2, s[day] == 2))
    solver.add(Or(oslo_full_days))
    
    # Dubrovnik full day constraint (days 5-9)
    dubrovnik_full_days = []
    for day in [5, 6, 7, 8, 9]:
        dubrovnik_full_days.append(And(s[day-1] == 3, s[day] == 3))
    solver.add(Or(dubrovnik_full_days))
    
    # Block previous invalid solution
    prev_solution = [0,0,0,0,0,1,1,1,3,3,3,3,4,4,4,4,2,2,2]
    block = Or([s[i] != prev_solution[i] for i in range(19)])
    solver.add(block)
    
    if solver.check() == sat:
        model = solver.model()
        s_vals = [model.evaluate(s[i]).as_long() for i in range(19)]
        
        for day in range(1, 19):
            start_city = s_vals[day-1]
            end_city = s_vals[day]
            if start_city == end_city:
                print(f"Day {day}: Stay in {cities[start_city]}")
            else:
                print(f"Day {day}: Travel from {cities[start_city]} to {cities[end_city]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
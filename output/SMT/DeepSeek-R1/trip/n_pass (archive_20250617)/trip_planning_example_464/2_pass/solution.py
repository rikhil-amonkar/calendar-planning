from z3 import *

def main():
    # City mapping: indices to names
    cities = ["Krakow", "Frankfurt", "Oslo", "Dubrovnik", "Naples"]
    # Allowed direct flights as tuples (city_index1, city_index2)
    allowed_pairs = [(0, 1), (0, 2), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]
    allowed_edges = []
    for a, b in allowed_pairs:
        allowed_edges.append((a, b))
        allowed_edges.append((b, a))
    
    # Required days per city: Krakow(0), Frankfurt(1), Oslo(2), Dubrovnik(3), Naples(4)
    required_days = [5, 4, 3, 5, 5]
    
    # Create Z3 variables: s1 to s19 (19 variables for 18 days)
    s = [Int('s%d' % i) for i in range(1, 20)]
    
    solver = Solver()
    
    # Each s_i must be between 0 and 4 (inclusive)
    for i in range(19):
        solver.add(s[i] >= 0, s[i] <= 4)
    
    # Flight constraints: if s_i != s_{i+1}, then (s_i, s_{i+1}) must be in allowed_edges
    for i in range(18):  # from s1 to s18 (for s_i and s_{i+1})
        edge_constraint = Or([And(s[i] == a, s[i+1] == b) for (a, b) in allowed_edges])
        solver.add(If(s[i] != s[i+1], edge_constraint, True))
    
    # Total days per city constraint
    for c in range(5):
        total = 0
        for i in range(18):  # i from 0 to 17, representing days 1 to 18
            total += If(Or(s[i] == c, s[i+1] == c), 1, 0)
        solver.add(total == required_days[c])
    
    # Constraint: At least one full day in Oslo (city index 2) between day 16 and day 18 (inclusive)
    oslo_full_days = []
    # Day 16: index 15 (s16 and s17)
    # Day 17: index 16 (s17 and s18)
    # Day 18: index 17 (s18 and s19)
    for i in range(15, 18):  # days 16, 17, 18
        oslo_full_days.append(And(s[i] == 2, s[i+1] == 2))
    solver.add(Or(oslo_full_days))
    
    # Constraint: At least one full day in Dubrovnik (city index 3) between day 5 and day 9 (inclusive)
    dubrovnik_full_days = []
    # Day 5: index 4 (s5 and s6)
    # Day 6: index 5 (s6 and s7)
    # Day 7: index 6 (s7 and s8)
    # Day 8: index 7 (s8 and s9)
    # Day 9: index 8 (s9 and s10)
    for i in range(4, 9):  # days 5 to 9
        dubrovnik_full_days.append(And(s[i] == 3, s[i+1] == 3))
    solver.add(Or(dubrovnik_full_days))
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        # Get the values for s1 to s19
        s_vals = [model.evaluate(s[i]).as_long() for i in range(19)]
        
        # Output the plan
        for day in range(1, 19):  # days 1 to 18
            idx = day - 1  # index in s_vals for the start of the day
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
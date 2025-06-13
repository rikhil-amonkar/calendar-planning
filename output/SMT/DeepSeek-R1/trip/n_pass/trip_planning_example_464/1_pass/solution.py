from z3 import *

def main():
    # City mapping: indices to names
    cities = ["Krakow", "Frankfurt", "Oslo", "Dubrovnik", "Naples"]
    # Allowed direct flights as tuples (city_index1, city_index2)
    allowed_edges_list = [(3, 2), (1, 0), (1, 2), (3, 1), (0, 2), (4, 2), (4, 3), (4, 1)]
    # Required days per city: Krakow(0), Frankfurt(1), Oslo(2), Dubrovnik(3), Naples(4)
    required_days = [5, 4, 3, 5, 5]
    
    # Create Z3 variables: s1 to s19 (19 variables for 18 days)
    s = [Int('s%d' % i) for i in range(1, 20)]
    
    solver = Solver()
    
    # Each s_i must be between 0 and 4 (inclusive)
    for i in range(19):
        solver.add(s[i] >= 0, s[i] <= 4)
    
    # Flight constraints: if s_i != s_{i+1}, then (s_i, s_{i+1}) must be in allowed_edges_list (considering both orders)
    for i in range(18):  # from s1 to s18 (for s_i and s_{i+1})
        edge_constraints = []
        for a, b in allowed_edges_list:
            # Either (s_i = a and s_{i+1} = b) or (s_i = b and s_{i+1} = a)
            edge_constraints.append(Or(And(s[i] == a, s[i+1] == b), And(s[i] == b, s[i+1] == a)))
        # If s_i != s_{i+1}, then one of the allowed edges must be used
        solver.add(Implies(s[i] != s[i+1], Or(edge_constraints)))
    
    # Total days per city constraint
    for c in range(5):
        total = 0
        for i in range(18):  # i from 0 to 17, representing days 1 to 18
            # Check if the city c is either the start (s_i) or end (s_{i+1}) of the day
            total += If(Or(s[i] == c, s[i+1] == c), 1, 0)
        solver.add(total == required_days[c])
    
    # Constraint: Oslo (city index 2) must be visited on at least one day between 16 and 18 (inclusive)
    # Days 16, 17, 18 correspond to indices 15, 16, 17 in the s array (since days start at 1, s[15] is s16, s[16] is s17, s[17] is s18, s[18] is s19)
    oslo_constraints = []
    # For day 16: we are in Oslo if s16 or s17 is Oslo -> s[15] or s[16] is 2
    oslo_constraints.append(Or(s[15] == 2, s[16] == 2))
    # For day 17: s17 or s18 -> s[16] or s[17] is 2
    oslo_constraints.append(Or(s[16] == 2, s[17] == 2))
    # For day 18: s18 or s19 -> s[17] or s[18] is 2
    oslo_constraints.append(Or(s[17] == 2, s[18] == 2))
    solver.add(Or(oslo_constraints))
    
    # Constraint: Dubrovnik (city index 3) must be visited on at least one day between 5 and 9 (inclusive)
    dubrovnik_constraints = []
    # Days 5 to 9: indices 4 to 8 in s (s[4] is s5, s[5] is s6, ..., s[8] is s9, s[9] is s10)
    for i in range(4, 9):  # for days 5 to 9: i from 4 to 8
        dubrovnik_constraints.append(Or(s[i] == 3, s[i+1] == 3))
    solver.add(Or(dubrovnik_constraints))
    
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
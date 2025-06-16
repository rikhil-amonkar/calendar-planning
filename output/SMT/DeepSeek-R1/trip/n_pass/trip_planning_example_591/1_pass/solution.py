import z3

def main():
    s = z3.Solver()
    
    # Cities: Stuttgart, Bucharest, Geneva, Valencia, Munich
    cities = {
        0: "Stuttgart",
        1: "Bucharest",
        2: "Geneva",
        3: "Valencia",
        4: "Munich"
    }
    n_days = 17
    n_cities = 5
    
    # Create variables for L_1 to L_17
    L = [z3.Int(f"L_{d+1}") for d in range(n_days)]
    
    # Constraint: Each L_d must be in [0, 4]
    for d in range(n_days):
        s.add(L[d] >= 0)
        s.add(L[d] < n_cities)
    
    # Required days per city: [Stuttgart, Bucharest, Geneva, Valencia, Munich]
    required = [2, 2, 4, 6, 7]
    
    # Total days per city constraint
    for i in range(n_cities):
        term1 = z3.Sum([z3.If(L[d] == i, 1, 0) for d in range(n_days)])
        term2 = z3.Sum([z3.If(z3.And(L[d] != L[d+1], L[d+1] == i), 1, 0) for d in range(n_days-1)])
        total_i = term1 + term2
        s.add(total_i == required[i])
    
    # Geneva must be only on days 1 to 4
    s.add(L[16] != 2)  # L_17 != Geneva
    for d in range(1, 17):  # d: actual day number (1 to 16)
        idx1 = d-1  # index for L_d
        idx2 = d    # index for L_{d+1}
        condition = z3.Or(L[idx1] == 2, z3.And(L[idx2] == 2, L[idx1] != L[idx2]))
        s.add(z3.Implies(condition, d <= 4))
    
    # Munich must be only on days 4 to 10
    s.add(L[16] != 4)  # L_17 != Munich
    for d in range(1, 17):  # d: actual day number (1 to 16)
        idx1 = d-1  # index for L_d
        idx2 = d    # index for L_{d+1}
        condition = z3.Or(L[idx1] == 4, z3.And(L[idx2] == 4, L[idx1] != L[idx2]))
        s.add(z3.Implies(condition, z3.And(d >= 4, d <= 10)))
    
    # Flight constraints: allowed direct flights (both directions)
    directed_edges = [
        (2, 4), (4, 2),  # Geneva-Munich
        (4, 3), (3, 4),  # Munich-Valencia
        (1, 3), (3, 1),  # Bucharest-Valencia
        (4, 1), (1, 4),  # Munich-Bucharest
        (3, 0), (0, 3),  # Valencia-Stuttgart
        (2, 3), (3, 2)   # Geneva-Valencia
    ]
    for d in range(0, n_days-1):  # d: index from 0 to 15 (days 1 to 16)
        # Constraint: if L_d != L_{d+1}, then (L_d, L_{d+1}) must be in directed_edges
        edge_condition = z3.Or([z3.And(L[d] == a, L[d+1] == b) for (a, b) in directed_edges])
        s.add(z3.Implies(L[d] != L[d+1], edge_condition))
    
    # Force Geneva on days 1, 2, 3, 4
    for d in [1, 2, 3, 4]:
        idx1 = d-1  # index for L_d
        if d < 4:
            condition = z3.Or(L[idx1] == 2, z3.And(L[d] == 2, L[idx1] != L[d]))
        else:  # d == 4
            condition = z3.Or(L[idx1] == 2, z3.And(L[4] == 2, L[idx1] != L[4]))
        s.add(condition)
    
    # Force Munich on days 4, 5, 6, 7, 8, 9, 10
    for d in range(4, 11):  # d: actual day number 4 to 10
        idx1 = d-1  # index for L_d
        if d < 10:
            condition = z3.Or(L[idx1] == 4, z3.And(L[d] == 4, L[idx1] != L[d]))
        else:  # d == 10
            condition = z3.Or(L[idx1] == 4, z3.And(L[10] == 4, L[idx1] != L[10]))
        s.add(condition)
    
    # Solve the problem
    if s.check() == z3.sat:
        m = s.model()
        plan = [m.evaluate(L[d]).as_long() for d in range(n_days)]
        
        # Determine the set of cities for each day
        schedule = []
        for d in range(n_days):
            if d == n_days-1:  # Last day: no travel
                cities_set = {plan[d]}
            else:
                if plan[d] == plan[d+1]:
                    cities_set = {plan[d]}
                else:
                    cities_set = {plan[d], plan[d+1]}
            schedule.append(cities_set)
        
        # Print the schedule
        for d in range(n_days):
            day = d + 1
            cities_list = sorted([cities[c] for c in schedule[d]])
            if len(cities_list) == 1:
                print(f"Day {day}: {cities_list[0]}")
            else:
                print(f"Day {day}: {cities_list[0]} and {cities_list[1]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
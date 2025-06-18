import z3

def main():
    s = z3.Solver()
    cities = ["Stuttgart", "Bucharest", "Geneva", "Valencia", "Munich"]
    required = [2, 2, 4, 6, 7]
    n_days = 17
    n_cities = len(cities)
    
    # Allowed flights as (from, to) pairs
    allowed_edges = [
        (2, 4), (4, 2),  # Geneva-Munich
        (4, 3), (3, 4),  # Munich-Valencia
        (1, 3), (3, 1),  # Bucharest-Valencia
        (4, 1), (1, 4),  # Munich-Bucharest
        (3, 0), (0, 3),  # Valencia-Stuttgart
        (2, 3), (3, 2)   # Geneva-Valencia
    ]
    
    # Decision variables: L[d] = starting city on day d (0-indexed)
    L = [z3.Int(f"L_{d}") for d in range(n_days)]
    for d in range(n_days):
        s.add(L[d] >= 0, L[d] < n_cities)
    
    # Presence function: true if in city i on day d
    def presence(d, i):
        if d < n_days - 1:
            return z3.Or(
                L[d] == i,  # Start day in city
                z3.And(L[d] != L[d+1], L[d+1] == i)  # Fly to city on day d
            )
        else:
            return L[d] == i  # Last day no flight
    
    # Total days per city constraint
    for i in range(n_cities):
        total_days = z3.Sum([z3.If(presence(d, i), 1, 0) for d in range(n_days)])
        s.add(total_days == required[i])
    
    # Geneva must be only between days 1-4
    for d in range(n_days):
        day_num = d + 1
        # If present in Geneva, must be day 1-4
        s.add(z3.Implies(presence(d, 2), day_num >= 1))
        s.add(z3.Implies(presence(d, 2), day_num <= 4))
    
    # Munich must be only between days 4-10
    for d in range(n_days):
        day_num = d + 1
        s.add(z3.Implies(presence(d, 4), day_num >= 4))
        s.add(z3.Implies(presence(d, 4), day_num <= 10))
    
    # Flight constraints
    for d in range(n_days - 1):
        edge_condition = z3.Or([
            z3.And(L[d] == a, L[d+1] == b) for (a, b) in allowed_edges
        ])
        s.add(z3.Implies(L[d] != L[d+1], edge_condition))
    
    # Solve and output
    if s.check() == z3.sat:
        m = s.model()
        L_vals = [m.evaluate(L[d]).as_long() for d in range(n_days)]
        
        # Build schedule: for each day, list of cities present
        schedule = []
        for d in range(n_days):
            cities_today = []
            # Check all cities for presence
            for i in range(n_cities):
                if d < n_days - 1:
                    if (L_vals[d] == i) or (L_vals[d] != L_vals[d+1] and L_vals[d+1] == i):
                        cities_today.append(cities[i])
                else:
                    if L_vals[d] == i:
                        cities_today.append(cities[i])
            schedule.append(cities_today)
        
        # Print schedule
        for d in range(n_days):
            day_num = d + 1
            cities_today = sorted(schedule[d])  # Sort for consistent order
            if len(cities_today) == 1:
                print(f"Day {day_num}: {cities_today[0]}")
            else:
                print(f"Day {day_num}: {cities_today[0]} and {cities_today[1]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
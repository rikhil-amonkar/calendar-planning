import z3

def main():
    s = z3.Solver()
    cities = ["Stuttgart", "Bucharest", "Geneva", "Valencia", "Munich"]
    n_days = 17
    n_cities = len(cities)
    
    # Allowed flights: (from, to) pairs
    allowed_edges = [
        (2, 4), (4, 2),  # Geneva <-> Munich
        (4, 3), (3, 4),  # Munich <-> Valencia
        (1, 3), (3, 1),  # Bucharest <-> Valencia
        (4, 1), (1, 4),  # Munich <-> Bucharest
        (3, 0), (0, 3),  # Valencia <-> Stuttgart
        (2, 3), (3, 2)   # Geneva <-> Valencia
    ]
    
    # Decision variables: L[d] = city on day d (0-indexed)
    L = [z3.Int(f"L_{d}") for d in range(n_days)]
    for d in range(n_days):
        s.add(L[d] >= 0, L[d] < n_cities)
    
    # Start in Geneva (index 2) on day 1, end in Stuttgart (index 0) on day 17
    s.add(L[0] == 2)  # Start in Geneva
    s.add(L[16] == 0)  # End in Stuttgart
    
    # Presence function: true if in city i on day d
    def presence(d, i):
        if d == 0:
            # First day: only start city
            return L[d] == i
        else:
            # On other days: either start in city or fly to city
            return z3.Or(L[d] == i,  # Start day in city
                         z3.And(L[d-1] != L[d], L[d] == i))  # Fly to city on day d
    
    # Total days per city constraint
    s.add(z3.Sum([z3.If(presence(0, 2), 1, 0)]) == 4)  # Geneva: 4 days
    s.add(z3.Sum([z3.If(presence(0, 4), 1, 0)]) == 7)  # Munich: 7 days
    s.add(z3.Sum([z3.If(presence(0, 1), 1, 0)]) == 2)  # Bucharest: 2 days
    s.add(z3.Sum([z3.If(presence(0, 3), 1, 0)]) == 6)  # Valencia: 6 days
    s.add(z3.Sum([z3.If(presence(0, 0), 1, 0)]) == 2)  # Stuttgart: 2 days
    
    # Geneva only on days 1-4 (index 0-3)
    for d in range(4, n_days):
        s.add(presence(d, 2) == False)
    
    # Munich only on days 4-10 (index 3-9)
    for d in range(0, 3):  # Days 1-3
        s.add(presence(d, 4) == False)
    for d in range(10, n_days):  # Days 11-17
        s.add(presence(d, 4) == False)
    
    # Flight constraints
    for d in range(n_days - 1):
        from_city = L[d]
        to_city = L[d+1]
        # If changing city, must be allowed flight
        edge_constraint = z3.Or([z3.And(from_city == a, to_city == b) for (a, b) in allowed_edges])
        s.add(z3.Implies(from_city != to_city, edge_constraint))
    
    # Solve and output
    if s.check() == z3.sat:
        m = s.model()
        L_vals = [m.evaluate(L[d]).as_long() for d in range(n_days)]
        
        # Build daily presence
        schedule = []
        for d in range(n_days):
            if d == 0:
                # First day: only start city
                cities_today = [cities[L_vals[0]]]
            else:
                # Other days: start city + arrival city if flight
                if L_vals[d-1] != L_vals[d]:
                    cities_today = sorted([cities[L_vals[d-1]], cities[L_vals[d]]])
                else:
                    cities_today = [cities[L_vals[d]]]
            schedule.append(cities_today)
        
        # Print schedule
        for d in range(n_days):
            day_num = d + 1
            if len(schedule[d]) == 1:
                print(f"Day {day_num}: {schedule[d][0]}")
            else:
                print(f"Day {day_num}: {schedule[d][0]} and {schedule[d][1]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
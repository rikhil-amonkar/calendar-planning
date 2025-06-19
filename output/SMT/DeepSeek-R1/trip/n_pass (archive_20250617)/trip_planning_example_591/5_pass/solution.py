import z3

def main():
    s = z3.Solver()
    cities = ["Stuttgart", "Bucharest", "Geneva", "Valencia", "Munich"]
    n_days = 17
    n_cities = len(cities)
    
    # Allowed flights
    allowed_edges = [
        (2, 4), (4, 2),  # Geneva <-> Munich
        (4, 3), (3, 4),  # Munich <-> Valencia
        (1, 3), (3, 1),  # Bucharest <-> Valencia
        (4, 1), (1, 4),  # Munich <-> Bucharest
        (3, 0), (0, 3),  # Valencia <-> Stuttgart
        (2, 3), (3, 2)   # Geneva <-> Valencia
    ]
    
    # Decision variables: L[d] = city on day d
    L = [z3.Int(f"L_{d}") for d in range(n_days)]
    for d in range(n_days):
        s.add(L[d] >= 0, L[d] < n_cities)
    
    # Start in Geneva (index 2) on day 1, end in Stuttgart (index 0) on day 17
    s.add(L[0] == 2)  # Start in Geneva
    s.add(L[16] == 0)  # End in Stuttgart
    
    # Presence function: true if in city i on day d
    def presence(d, i):
        if d < n_days - 1:
            return z3.Or(L[d] == i,  # Start day in city
                         z3.And(L[d] != L[d+1], L[d+1] == i))  # Fly to city at end of day
        else:
            return L[d] == i  # Last day no flight
    
    # Total days per city constraint
    total_days = []
    for i in range(n_cities):
        total_days.append(z3.Sum([z3.If(presence(d, i), 1, 0) for d in range(n_days)]))
    s.add(total_days[2] == 4)  # Geneva: 4 days
    s.add(total_days[4] == 7)  # Munich: 7 days
    s.add(total_days[1] == 2)  # Bucharest: 2 days
    s.add(total_days[3] == 6)  # Valencia: 6 days
    s.add(total_days[0] == 2)  # Stuttgart: 2 days
    
    # Geneva only on days 1-4 (0-indexed days 0-3)
    for d in range(4, n_days):
        s.add(z3.Not(presence(d, 2)))
    
    # Munich only on days 4-10 (0-indexed days 3-9)
    for d in range(0, 3):  # Days 1-3 (0-indexed 0-2)
        s.add(z3.Not(presence(d, 4)))
    for d in range(10, n_days):  # Days 11-17 (0-indexed 10-16)
        s.add(z3.Not(presence(d, 4)))
    
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
            cities_today = []
            # Current city
            current_city = L_vals[d]
            cities_today.append(cities[current_city])
            # If flight at end of day, add next city
            if d < n_days - 1 and L_vals[d] != L_vals[d+1]:
                cities_today.append(cities[L_vals[d+1]])
            schedule.append(sorted(cities_today))  # Sort for consistent order
        
        # Print schedule
        for d in range(n_days):
            day_num = d + 1
            cities_today = schedule[d]
            if len(cities_today) == 1:
                print(f"Day {day_num}: {cities_today[0]}")
            else:
                print(f"Day {day_num}: {cities_today[0]} and {cities_today[1]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
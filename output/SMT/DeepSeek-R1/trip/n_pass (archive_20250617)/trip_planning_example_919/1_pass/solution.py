from z3 import *

def main():
    # City mapping: 0 to 6 for the 7 cities
    cities = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]
    n_days = 15

    # Define bidirectional connections (undirected edges)
    bidirectional_undirected = [
        (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6),
        (1, 3), (1, 4), (1, 5), (1, 6),
        (2, 4), (2, 6),
        (3, 4), (3, 6),
        (4, 6),
        (5, 6)
    ]
    
    # Create directed edges: bidirectional edges in both directions plus unidirectional edges
    directed_edges = []
    for (u, v) in bidirectional_undirected:
        directed_edges.append((u, v))
        directed_edges.append((v, u))
    directed_edges.append((2, 3))  # Rome to Riga (unidirectional)
    directed_edges.append((3, 5))  # Riga to Vilnius (unidirectional)

    # Create Z3 variables: a[i] and b[i] for each day i
    a = [Int(f'a_{i}') for i in range(n_days)]
    b = [Int(f'b_{i}') for i in range(n_days)]
    
    s = Solver()
    
    # Each a[i] and b[i] must be between 0 and 6 (inclusive)
    for i in range(n_days):
        s.add(And(a[i] >= 0, a[i] <= 6))
        s.add(And(b[i] >= 0, b[i] <= 6))
    
    # Consistency: b[i] must equal a[i+1] for i from 0 to 13
    for i in range(n_days - 1):
        s.add(b[i] == a[i + 1])
    
    # Flight constraints: if a[i] != b[i], then (a[i], b[i]) must be in directed_edges
    for i in range(n_days):
        edge_constraints = []
        for (u, v) in directed_edges:
            edge_constraints.append(And(a[i] == u, b[i] == v))
        s.add(If(a[i] != b[i], Or(edge_constraints), True))
    
    # Count days in each city
    total_days = [0] * 7
    for c in range(7):
        total_days[c] = Sum([If(Or(a[i] == c, b[i] == c), 1, 0) for i in range(n_days)])
    
    # Add constraints for required days per city
    s.add(total_days[0] == 4)  # Vienna
    s.add(total_days[1] == 2)  # Milan
    s.add(total_days[2] == 3)  # Rome
    s.add(total_days[3] == 2)  # Riga
    s.add(total_days[4] == 3)  # Lisbon
    s.add(total_days[5] == 4)  # Vilnius
    s.add(total_days[6] == 3)  # Oslo
    
    # Fixed events: must be in Vienna on day 1 (index 0) and day 4 (index 3)
    s.add(Or(a[0] == 0, b[0] == 0))
    s.add(Or(a[3] == 0, b[3] == 0))
    
    # Must be in Lisbon on at least one day from 11 to 13 (indices 10, 11, 12)
    lisbon_constraint = Or(
        Or(a[10] == 4, b[10] == 4),
        Or(a[11] == 4, b[11] == 4),
        Or(a[12] == 4, b[12] == 4)
    )
    s.add(lisbon_constraint)
    
    # Must be in Oslo on at least one day from 13 to 15 (indices 12, 13, 14)
    oslo_constraint = Or(
        Or(a[12] == 6, b[12] == 6),
        Or(a[13] == 6, b[13] == 6),
        Or(a[14] == 6, b[14] == 6)
    )
    s.add(oslo_constraint)
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        plan = []
        for i in range(n_days):
            a_val = m.evaluate(a[i])
            b_val = m.evaluate(b[i])
            a_city = cities[int(str(a_val))]
            b_city = cities[int(str(b_val))]
            if a_val == b_val:
                cities_today = [a_city]
            else:
                cities_today = [a_city, b_city]
            plan.append((i + 1, cities_today))
        
        # Output the plan
        for day, cities_list in plan:
            print(f"Day {day}: {', '.join(cities_list)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
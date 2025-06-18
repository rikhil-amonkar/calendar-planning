from z3 import *

def main():
    cities = ['Zurich', 'Helsinki', 'Hamburg', 'Bucharest', 'Split']
    n_cities = len(cities)
    n_days = 12
    required_days = [3, 2, 2, 2, 7]  # Zurich, Helsinki, Hamburg, Bucharest, Split
    
    # Define allowed directed flights (both directions for each undirected pair)
    allowed_edges = [
        (0, 1), (1, 0),  # Zurich-Helsinki
        (2, 3), (3, 2),  # Hamburg-Bucharest
        (1, 2), (2, 1),  # Helsinki-Hamburg
        (0, 2), (2, 0),  # Zurich-Hamburg
        (0, 3), (3, 0),  # Zurich-Bucharest
        (0, 4), (4, 0),  # Zurich-Split
        (1, 4), (4, 1),  # Helsinki-Split
        (2, 4), (4, 2)   # Split-Hamburg
    ]
    
    # Create Z3 variables for end city each day
    end = [Int(f'end_{d}') for d in range(n_days)]
    # Start city for day0 is free; for d>0, start[d] = end[d-1]
    s = Solver()
    
    # Domain constraints: end cities are 0-4
    for d in range(n_days):
        s.add(end[d] >= 0, end[d] < n_cities)
    
    # Start city for day0 is not constrained, but we'll compute it
    # For d>0: start[d] = end[d-1]
    # Travel constraint: if start[d] != end[d], then flight must be allowed
    for d in range(n_days):
        if d == 0:
            start_d = Int('start_0')
            s.add(start_d >= 0, start_d < n_cities)
        else:
            start_d = end[d-1]
        
        # If not staying, ensure flight is allowed
        flight_constraint = Or([And(start_d == a, end[d] == b) for (a, b) in allowed_edges])
        s.add(If(start_d == end[d], True, flight_constraint))
    
    # Wedding constraint: must be in Zurich at the end of one of the first three days
    s.add(Or(end[0] == 0, end[1] == 0, end[2] == 0))
    
    # Conference constraint: must be in Split at the end of day4 and day10
    s.add(end[3] == 4)  # Day4 (0-indexed day3)
    s.add(end[9] == 4)  # Day10 (0-indexed day9)
    
    # Total days per city constraint (based on end city)
    for c in range(n_cities):
        total = 0
        for d in range(n_days):
            total += If(end[d] == c, 1, 0)
        s.add(total == required_days[c])
    
    # Solve and print schedule
    if s.check() == sat:
        m = s.model()
        # Get start city for day0
        start0_val = m.evaluate(Int('start_0')).as_long() if n_days > 0 else 0
        end_vals = [m.evaluate(end[d]).as_long() for d in range(n_days)]
        
        print("Day\tStart City\tEnd City\tDescription")
        for d in range(n_days):
            if d == 0:
                start_city = cities[start0_val]
            else:
                start_city = cities[end_vals[d-1]]
            end_city = cities[end_vals[d]]
            if start_city == end_city:
                desc = f"Stay in {start_city}"
            else:
                desc = f"Travel from {start_city} to {end_city}"
            print(f"{d+1}\t{start_city}\t\t{end_city}\t\t{desc}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()
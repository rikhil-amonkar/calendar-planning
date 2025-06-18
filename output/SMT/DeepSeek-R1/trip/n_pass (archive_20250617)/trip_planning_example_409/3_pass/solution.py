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
    
    # Create Z3 variables for start and end cities each day
    start = [Int(f'start_{d}') for d in range(n_days)]
    end = [Int(f'end_{d}') for d in range(n_days)]
    
    s = Solver()
    
    # Domain constraints: cities are 0-4
    for d in range(n_days):
        s.add(start[d] >= 0, start[d] < n_cities)
        s.add(end[d] >= 0, end[d] < n_cities)
    
    # Continuity: end city of day d must match start city of day d+1
    for d in range(n_days - 1):
        s.add(end[d] == start[d+1])
    
    # Travel constraint: if start != end, must be allowed flight
    for d in range(n_days):
        flight_possible = Or([And(start[d] == a, end[d] == b) for (a, b) in allowed_edges])
        s.add(If(start[d] != end[d], flight_possible, True))
    
    # Wedding constraint: must be in Zurich on at least one of days 1-3
    wedding_days = []
    for d in range(3):  # Days 0,1,2 (1,2,3 in 1-indexing)
        wedding_days.append(Or(start[d] == 0, end[d] == 0))
    s.add(Or(wedding_days))
    
    # Conference constraint: must be in Split on days 4 and 10
    s.add(Or(start[3] == 4, end[3] == 4))  # Day 4 (index 3)
    s.add(Or(start[9] == 4, end[9] == 4))  # Day 10 (index 9)
    
    # Total days per city constraint
    for c in range(n_cities):
        total = 0
        for d in range(n_days):
            # Count 1 if city is start city
            total += If(start[d] == c, 1, 0)
            # Count 1 if city is end city and different from start city
            total += If(And(end[d] == c, start[d] != c), 1, 0)
        s.add(total == required_days[c])
    
    # Solve and print schedule
    if s.check() == sat:
        m = s.model()
        start_vals = [m.evaluate(start[d]).as_long() for d in range(n_days)]
        end_vals = [m.evaluate(end[d]).as_long() for d in range(n_days)]
        
        print("Day\tStart City\tEnd City\tDescription")
        for d in range(n_days):
            start_city = cities[start_vals[d]]
            end_city = cities[end_vals[d]]
            if start_vals[d] == end_vals[d]:
                desc = f"Stay in {start_city}"
            else:
                desc = f"Travel from {start_city} to {end_city}"
            print(f"{d+1}\t{start_city}\t\t{end_city}\t\t{desc}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()
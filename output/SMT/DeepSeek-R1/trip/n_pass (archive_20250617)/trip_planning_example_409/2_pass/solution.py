from z3 import *

def main():
    # Define city names and their indices
    cities = ['Zurich', 'Helsinki', 'Hamburg', 'Bucharest', 'Split']
    n_cities = len(cities)
    n_days = 12
    
    # Required days per city: [Zurich, Helsinki, Hamburg, Bucharest, Split]
    required = [3, 2, 2, 2, 7]
    
    # Define undirected edges (both directions included)
    undir_edges = [
        (0, 1), (0, 2), (0, 3), (0, 4),
        (1, 2), (1, 4),
        (2, 3), (2, 4)
    ]
    allowed_edges = []
    for (a, b) in undir_edges:
        allowed_edges.append((a, b))
        allowed_edges.append((b, a))
    
    # Create Z3 variables
    start_city = [Int('start_city_%d' % d) for d in range(n_days)]
    end_city = [Int('end_city_%d' % d) for d in range(n_days)]
    
    s = Solver()
    
    # Domain constraints for start and end cities
    for d in range(n_days):
        s.add(start_city[d] >= 0, start_city[d] < n_cities)
        s.add(end_city[d] >= 0, end_city[d] < n_cities)
    
    # Continuity constraint: end_city of day d must equal start_city of day d+1
    for d in range(n_days - 1):
        s.add(end_city[d] == start_city[d + 1])
    
    # Direct flight constraint for travel days
    for d in range(n_days):
        travel_condition = start_city[d] != end_city[d]
        edge_constraints = []
        for (a, b) in allowed_edges:
            edge_constraints.append(And(start_city[d] == a, end_city[d] == b))
        s.add(If(travel_condition, Or(edge_constraints), True))
    
    # Event constraints: Split on days 4 and 10 (0-indexed days 3 and 9)
    s.add(Or(start_city[3] == 4, end_city[3] == 4))  # Day 4
    s.add(Or(start_city[9] == 4, end_city[9] == 4))  # Day 10
    
    # Wedding in Zurich between days 1 and 3 (0-indexed days 0, 1, 2)
    wedding_constraint = Or(
        Or(start_city[0] == 0, end_city[0] == 0),
        Or(start_city[1] == 0, end_city[1] == 0),
        Or(start_city[2] == 0, end_city[2] == 0)
    )
    s.add(wedding_constraint)
    
    # Total days per city constraint
    for c in range(n_cities):
        total_days = 0
        for d in range(n_days):
            total_days += If(Or(start_city[d] == c, end_city[d] == c), 1, 0)
        s.add(total_days == required[c])
    
    # Check for solution and print
    if s.check() == sat:
        m = s.model()
        start_vals = [m.evaluate(start_city[d]).as_long() for d in range(n_days)]
        end_vals = [m.evaluate(end_city[d]).as_long() for d in range(n_days)]
        
        # Print itinerary
        print("Day\tStart City\tEnd City\tDescription")
        for d in range(n_days):
            start_city_name = cities[start_vals[d]]
            end_city_name = cities[end_vals[d]]
            if start_vals[d] == end_vals[d]:
                desc = f"Stay in {start_city_name}"
            else:
                desc = f"Travel from {start_city_name} to {end_city_name}"
            print(f"{d+1}\t{start_city_name}\t\t{end_city_name}\t\t{desc}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()
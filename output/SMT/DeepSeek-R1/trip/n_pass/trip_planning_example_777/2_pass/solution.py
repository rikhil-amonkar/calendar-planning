from z3 import *

def main():
    # Cities and their required stay durations
    cities = ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn']
    days_req = [5, 3, 3, 2, 2, 5]  # Corresponding to the cities list

    # Direct flight connections (undirected)
    edges_raw = [
        ('Helsinki', 'Riga'),
        ('Riga', 'Tallinn'),
        ('Vienna', 'Helsinki'),
        ('Riga', 'Dublin'),
        ('Vienna', 'Riga'),
        ('Reykjavik', 'Vienna'),
        ('Helsinki', 'Dublin'),
        ('Tallinn', 'Dublin'),
        ('Reykjavik', 'Helsinki'),
        ('Reykjavik', 'Dublin'),
        ('Helsinki', 'Tallinn'),
        ('Vienna', 'Dublin')
    ]
    
    # Create a set of edges in canonical form (sorted tuple)
    edge_set = set()
    for a, b in edges_raw:
        key = tuple(sorted([a, b]))
        edge_set.add(key)
    
    # Build a connectivity matrix: M[i][j] = True if there is a direct flight
    n = len(cities)
    M = [[False] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i != j:
                key = tuple(sorted([cities[i], cities[j]]))
                if key in edge_set:
                    M[i][j] = True

    # Initialize Z3 solver
    s = Solver()
    
    # Define the order as a permutation of 6 integers (0 to 5)
    order = [Int(f'o{i}') for i in range(n)]
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    s.add(Distinct(order))
    
    # Flight constraints: consecutive cities must have a direct flight
    for k in range(n-1):
        i = order[k]
        j = order[k+1]
        # Use the connectivity matrix M
        s.add(Or([And(i == idx_i, j == idx_j, M[idx_i][idx_j]) for idx_i in range(n) for idx_j in range(n)]))
    
    # Define the required days for each position in the order
    reqs = [Int(f'req_{i}') for i in range(n)]
    for i in range(n):
        # reqs[i] should be days_req[order[i]]
        cases = [And(order[i] == j, reqs[i] == days_req[j]) for j in range(n)]
        s.add(Or(cases))
    
    # Define prefix_sum for start day calculations
    prefix_sum = [Int(f'prefix_sum{i}') for i in range(n+1)]
    s.add(prefix_sum[0] == 0)
    for i in range(1, n+1):
        s.add(prefix_sum[i] == prefix_sum[i-1] + (reqs[i-1] - 1))
    
    # Total days constraint: the last day is prefix_sum[n] + 1 = 15
    s.add(prefix_sum[n] + 1 == 15)
    
    # Define positions for event cities
    pos_helsinki = Int('pos_helsinki')
    pos_vienna = Int('pos_vienna')
    pos_tallinn = Int('pos_tallinn')
    s.add(pos_helsinki >= 0, pos_helsinki < n)
    s.add(pos_vienna >= 0, pos_vienna < n)
    s.add(pos_tallinn >= 0, pos_tallinn < n)
    
    # Constraints for positions: for each city, there is a position j in the order where it appears
    s.add(Or([And(order[j] == 1, pos_helsinki == j) for j in range(n)]))
    s.add(Or([And(order[j] == 4, pos_vienna == j) for j in range(n)]))
    s.add(Or([And(order[j] == 5, pos_tallinn == j) for j in range(n)]))
    
    # Event constraints
    # Helsinki: 3 days, must have at least one day between day 3 and 5
    start_helsinki = Int('start_helsinki')
    end_helsinki = Int('end_helsinki')
    s.add(start_helsinki == 1 + prefix_sum[pos_helsinki])
    s.add(end_helsinki == start_helsinki + 2)  # 3 days: start, start+1, start+2
    s.add(start_helsinki <= 5, end_helsinki >= 3)
    
    # Vienna: 2 days, must have at least one day between day 2 and 3
    start_vienna = Int('start_vienna')
    end_vienna = Int('end_vienna')
    s.add(start_vienna == 1 + prefix_sum[pos_vienna])
    s.add(end_vienna == start_vienna + 1)  # 2 days: start, start+1
    s.add(start_vienna <= 3, end_vienna >= 2)
    
    # Tallinn: 5 days, must have at least one day between day 7 and 11
    start_tallinn = Int('start_tallinn')
    end_tallinn = Int('end_tallinn')
    s.add(start_tallinn == 1 + prefix_sum[pos_tallinn])
    s.add(end_tallinn == start_tallinn + 4)  # 5 days: start to start+4
    s.add(start_tallinn <= 11, end_tallinn >= 7)
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        # Extract the order
        order_val = [m.evaluate(order[i]).as_long() for i in range(n)]
        # Extract prefix sums
        prefix_sum_val = [m.evaluate(prefix_sum[i]).as_long() for i in range(n+1)]
        
        # Compute start and end days for each city in the order
        starts = []
        ends = []
        for i in range(n):
            start_day = 1 + prefix_sum_val[i]
            city_idx = order_val[i]
            length = days_req[city_idx]
            end_day = start_day + length - 1
            starts.append(start_day)
            ends.append(end_day)
        
        # Build the itinerary
        itinerary = []
        for i in range(n):
            start_i = starts[i]
            end_i = ends[i]
            city_name = cities[order_val[i]]
            # Add the contiguous stay
            if start_i == end_i:
                day_range_str = f"Day {start_i}"
            else:
                day_range_str = f"Day {start_i}-{end_i}"
            itinerary.append({"day_range": day_range_str, "place": city_name})
            # If not the last city, add the travel day records
            if i < n-1:
                # Departure from current city
                itinerary.append({"day_range": f"Day {end_i}", "place": city_name})
                # Arrival at next city
                next_city_name = cities[order_val[i+1]]
                itinerary.append({"day_range": f"Day {end_i}", "place": next_city_name})
        
        # Output the result
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
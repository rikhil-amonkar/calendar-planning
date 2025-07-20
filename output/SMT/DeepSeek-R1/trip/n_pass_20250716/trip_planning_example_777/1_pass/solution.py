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
        s.add(Or(
            And(i == idx_i, j == idx_j, M[idx_i][idx_j])
            for idx_i in range(n) for idx_j in range(n)
        ))
    
    # Define prefix_sum for start day calculations
    prefix_sum = [Int(f'prefix_sum{i}') for i in range(n+1)]
    s.add(prefix_sum[0] == 0)
    for i in range(1, n+1):
        # City index at position i-1 in the order
        city_idx = order[i-1]
        # Get the required days for this city
        req = days_req[city_idx]
        s.add(prefix_sum[i] == prefix_sum[i-1] + (req - 1))
    
    # Event constraints
    # Helsinki (city index 1) must have at least one day between day 3 and 5
    start_day_h = Int('start_day_h')
    end_day_h = Int('end_day_h')
    s.add(start_day_h == 1 + prefix_sum[1])
    s.add(end_day_h == start_day_h + 3 - 1)  # Helsinki is 3 days
    s.add(start_day_h <= 5, end_day_h >= 3)
    
    # Vienna (city index 4) must have at least one day between day 2 and 3
    start_day_v = Int('start_day_v')
    end_day_v = Int('end_day_v')
    s.add(start_day_v == 1 + prefix_sum[4])
    s.add(end_day_v == start_day_v + 2 - 1)  # Vienna is 2 days
    s.add(start_day_v <= 3, end_day_v >= 2)
    
    # Tallinn (city index 5) must have at least one day between day 7 and 11
    start_day_t = Int('start_day_t')
    end_day_t = Int('end_day_t')
    s.add(start_day_t == 1 + prefix_sum[5])
    s.add(end_day_t == start_day_t + 5 - 1)  # Tallinn is 5 days
    s.add(start_day_t <= 11, end_day_t >= 7)
    
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
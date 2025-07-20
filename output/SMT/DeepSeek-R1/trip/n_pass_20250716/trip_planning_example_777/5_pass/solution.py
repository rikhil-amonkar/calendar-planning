from z3 import *

def main():
    cities = ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn']
    days_req = [5, 3, 3, 2, 2, 5]

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
    
    edge_set = set()
    for a, b in edges_raw:
        key = tuple(sorted([a, b]))
        edge_set.add(key)
    
    n = len(cities)
    M = [[False] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i != j:
                key = tuple(sorted([cities[i], cities[j]]))
                if key in edge_set:
                    M[i][j] = True

    s = Solver()
    
    order = [Int(f'o{i}') for i in range(n)]
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    s.add(Distinct(order))
    
    for k in range(n-1):
        i = order[k]
        j = order[k+1]
        s.add(Or([And(i == idx_i, j == idx_j, M[idx_i][idx_j]) for idx_i in range(n) for idx_j in range(n)]))
    
    reqs = [Int(f'req_{i}') for i in range(n)]
    for i in range(n):
        cases = [And(order[i] == j, reqs[i] == days_req[j]) for j in range(n)]
        s.add(Or(cases))
    
    prefix_sum = [Int(f'prefix_sum{i}') for i in range(n+1)]
    s.add(prefix_sum[0] == 0)
    for i in range(1, n+1):
        s.add(prefix_sum[i] == prefix_sum[i-1] + (reqs[i-1] - 1))
    
    s.add(prefix_sum[n] + 1 == 15)
    
    # Helsinki: middle day (full day) must be between 3-5
    start_helsinki = 1 + Sum([If(order[j] == 1, prefix_sum[j], 0) for j in range(n)])
    s.add(start_helsinki + 1 >= 3, start_helsinki + 1 <= 5)
    
    # Vienna: must cover both days 2 and 3 (no full days possible)
    start_vienna = 1 + Sum([If(order[j] == 4, prefix_sum[j], 0) for j in range(n)])
    end_vienna = start_vienna + 1
    s.add(start_vienna <= 2, end_vienna >= 3)
    
    # Tallinn: must overlap with 7-11
    start_tallinn = 1 + Sum([If(order[j] == 5, prefix_sum[j], 0) for j in range(n)])
    end_tallinn = start_tallinn + 4
    s.add(start_tallinn <= 11, end_tallinn >= 7)
    
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(n)]
        prefix_sum_val = [m.evaluate(prefix_sum[i]).as_long() for i in range(n+1)]
        
        starts = []
        ends = []
        for i in range(n):
            start_day = 1 + prefix_sum_val[i]
            city_idx = order_val[i]
            length = days_req[city_idx]
            end_day = start_day + length - 1
            starts.append(start_day)
            ends.append(end_day)
        
        itinerary = []
        for i in range(n):
            start_i = starts[i]
            end_i = ends[i]
            city_name = cities[order_val[i]]
            if start_i == end_i:
                day_range_str = f"Day {start_i}"
            else:
                day_range_str = f"Day {start_i}-{end_i}"
            itinerary.append({"day_range": day_range_str, "place": city_name})
            if i < n-1:
                itinerary.append({"day_range": f"Day {end_i}", "place": city_name})
                next_city_name = cities[order_val[i+1]]
                itinerary.append({"day_range": f"Day {end_i}", "place": next_city_name})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
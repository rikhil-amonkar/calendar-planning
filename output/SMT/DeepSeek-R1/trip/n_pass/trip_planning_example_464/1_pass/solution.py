import z3
import json

def main():
    d_dict = {0: 5, 1: 4, 2: 5, 3: 5, 4: 3}
    city_names = {0: 'Dubrovnik', 1: 'Frankfurt', 2: 'Krakow', 3: 'Naples', 4: 'Oslo'}
    
    valid_edges = set()
    edges = [(0,4), (1,2), (1,4), (0,1), (2,4), (3,4), (0,3), (1,3)]
    for u, v in edges:
        valid_edges.add((u, v))
        valid_edges.add((v, u))
    valid_edges = list(valid_edges)
    
    s = z3.Solver()
    order = [z3.Int(f'o{i}') for i in range(4)]
    
    for i in range(4):
        s.add(order[i] >= 0, order[i] <= 3)
    s.add(z3.Distinct(order))
    
    cities_seq = [order[0], order[1], order[2], order[3], 4]
    
    start = [1] * 5
    for i in range(1, 5):
        prev_city = cities_seq[i-1]
        prev_days = d_dict[prev_city]
        start[i] = start[i-1] + (prev_days - 1)
    
    s.add(start[4] == 16)
    
    for i in range(4):
        city_val = cities_seq[i]
        s.add(z3.If(city_val == 0, start[i] <= 9, True))
    
    for i in range(4):
        a = cities_seq[i]
        b = cities_seq[i+1]
        cond = z3.Or([z3.And(a == u, b == v) for u, v in valid_edges])
        s.add(cond)
    
    if s.check() == z3.sat:
        m = s.model()
        order_vals = [m[var].as_long() for var in order]
        seq = order_vals + [4]
        
        starts = [1]
        for i in range(4):
            city_index = seq[i]
            days = d_dict[city_index]
            next_start = starts[-1] + (days - 1)
            starts.append(next_start)
        
        itinerary = []
        for i in range(5):
            city_idx = seq[i]
            name = city_names[city_idx]
            s_i = starts[i]
            d_val = d_dict[city_idx]
            e_i = s_i + d_val - 1
            
            if i != 0:
                itinerary.append({"day_range": f"Day {s_i}", "place": name})
            
            if i == 4:
                if s_i < e_i:
                    itinerary.append({"day_range": f"Day {s_i+1}-{e_i}", "place": name})
            else:
                itinerary.append({"day_range": f"Day {s_i}-{e_i}", "place": name})
            
            if i != 4:
                itinerary.append({"day_range": f"Day {e_i}", "place": name})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()
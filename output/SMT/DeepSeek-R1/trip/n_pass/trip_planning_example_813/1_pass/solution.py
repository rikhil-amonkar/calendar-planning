import z3
import json

def main():
    city_names = ['Seville', 'Vilnius', 'Santorini', 'London', 'Stuttgart', 'Dublin', 'Frankfurt']
    durations_arr = [5, 3, 2, 2, 3, 3, 5]
    city_index = {city: idx for idx, city in enumerate(city_names)}
    index_city = {idx: city for city, idx in city_index.items()}
    
    flights_raw = [
        ('Frankfurt', 'Dublin'),
        ('Frankfurt', 'London'),
        ('London', 'Dublin'),
        ('Vilnius', 'Frankfurt'),
        ('Frankfurt', 'Stuttgart'),
        ('Dublin', 'Seville'),
        ('London', 'Santorini'),
        ('Stuttgart', 'London'),
        ('Santorini', 'Dublin')
    ]
    flight_pairs = set()
    for a, b in flights_raw:
        i1 = city_index[a]
        i2 = city_index[b]
        flight_pairs.add((i1, i2))
        flight_pairs.add((i2, i1))
    
    order = [z3.Int(f"order_{i}") for i in range(7)]
    s = z3.Solver()
    
    for i in range(7):
        s.add(order[i] >= 0, order[i] <= 6)
    s.add(z3.Distinct(order))
    
    prefix_sum = [0] * 8
    prefix_sum[0] = 0
    for j in range(1, 8):
        dur = z3.Sum([z3.If(order[j-1] == k, durations_arr[k], 0) for k in range(7)])
        prefix_sum[j] = prefix_sum[j-1] + dur
    
    stuttgart_idx = city_index['Stuttgart']
    for i in range(7):
        cond = (order[i] == stuttgart_idx)
        s.add(z3.Implies(cond, prefix_sum[i] - i == 6))
    
    london_idx = city_index['London']
    for i in range(7):
        cond = (order[i] == london_idx)
        s_i = 1 + prefix_sum[i] - i
        s.add(z3.Implies(cond, z3.Or(s_i == 8, s_i == 9, s_i == 10)))
    
    for i in range(6):
        a = order[i]
        b = order[i+1]
        constraints = [z3.And(a == x, b == y) for (x, y) in flight_pairs]
        s.add(z3.Or(constraints))
    
    if s.check() == z3.sat:
        m = s.model()
        order_vals = [m[order[i]].as_long() for i in range(7)]
        prefix_sum_vals = [0]
        for i in range(7):
            city_idx = order_vals[i]
            dur = durations_arr[city_idx]
            prefix_sum_vals.append(prefix_sum_vals[-1] + dur)
        
        starts = []
        ends = []
        for i in range(7):
            s_i = 1 + prefix_sum_vals[i] - i
            dur = durations_arr[order_vals[i]]
            e_i = s_i + dur - 1
            starts.append(s_i)
            ends.append(e_i)
        
        itinerary = []
        for i in range(7):
            s_i = starts[i]
            e_i = ends[i]
            city_name = index_city[order_vals[i]]
            if s_i == e_i:
                day_range_str = f"Day {s_i}"
            else:
                day_range_str = f"Day {s_i}-{e_i}"
            itinerary.append({"day_range": day_range_str, "place": city_name})
            if i < 6:
                d = e_i
                next_city_name = index_city[order_vals[i+1]]
                itinerary.append({"day_range": f"Day {d}", "place": city_name})
                itinerary.append({"day_range": f"Day {d}", "place": next_city_name})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()
from z3 import *
import json

def main():
    cities = ["Brussels", "Bucharest", "Stuttgart", "Mykonos", "Helsinki", "Split", "London"]
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    durations_list = [4, 3, 4, 2, 5, 3, 5]
    
    edges_list = [
        (4, 6),  # Helsinki and London
        (0, 6),  # Brussels and London
        (1, 6),  # Bucharest and London
        (0, 1),  # Brussels and Bucharest
        (5, 4),  # Split and Helsinki
        (2, 6),  # Stuttgart and London
        (4, 0),  # Helsinki and Brussels
        (5, 6),  # Split and London
        (2, 5),  # Stuttgart and Split
        (6, 3)   # London and Mykonos
    ]
    non_madrid_edges = set()
    for a, b in edges_list:
        non_madrid_edges.add((min(a, b), max(a, b)))
    
    madrid_connected = {0, 1, 3, 4, 5, 6}  # All cities except Stuttgart (2)

    order = [Int(f'order_{i}') for i in range(7)]
    s = Solver()
    
    for i in range(7):
        s.add(order[i] >= 0, order[i] < 7)
    s.add(Distinct(order))
    
    start = [Int(f'start_{i}') for i in range(7)]
    s.add(start[0] == 1)
    for i in range(1, 7):
        d_prev = Int(f'd_prev_{i}')
        d_prev_expr = Sum([If(order[i-1] == j, durations_list[j], 0) for j in range(7)])
        s.add(d_prev == d_prev_expr)
        s.add(start[i] == start[i-1] + d_prev - 1)
    
    stuttgart_start = Sum([If(order[i] == 2, start[i], 0) for i in range(7)])
    s.add(stuttgart_start <= 4)
    
    for i in range(6):
        a = order[i]
        b = order[i+1]
        constraints = []
        for edge in non_madrid_edges:
            u, v = edge
            constraints.append(And(a == u, b == v))
            constraints.append(And(a == v, b == u))
        s.add(Or(constraints))
    
    s.add(Or([order[6] == idx for idx in madrid_connected]))
    
    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(order[i]).as_long() for i in range(7)]
        city_names = [int_to_city[idx] for idx in order_vals]
        
        starts = [1]
        for i in range(1, 7):
            prev_city = order_vals[i-1]
            prev_duration = durations_list[prev_city]
            starts.append(starts[i-1] + prev_duration - 1)
        ends = [starts[i] + durations_list[order_vals[i]] - 1 for i in range(7)]
        
        def format_day_range(start_day, end_day):
            if start_day == end_day:
                return f"Day {start_day}"
            else:
                return f"Day {start_day}-{end_day}"
        
        itinerary = []
        for i in range(7):
            city_name = int_to_city[order_vals[i]]
            start_day = starts[i]
            end_day = ends[i]
            itinerary.append({
                "day_range": format_day_range(start_day, end_day),
                "place": city_name
            })
            itinerary.append({
                "day_range": f"Day {end_day}",
                "place": city_name
            })
            if i < 6:
                next_city_name = int_to_city[order_vals[i+1]]
            else:
                next_city_name = "Madrid"
            itinerary.append({
                "day_range": f"Day {end_day}",
                "place": next_city_name
            })
        
        itinerary.append({
            "day_range": "Day 20-21",
            "place": "Madrid"
        })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
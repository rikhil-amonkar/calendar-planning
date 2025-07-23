from z3 import *
import json

def main():
    city_names = ['Venice', 'Barcelona', 'Copenhagen', 'Lyon', 'Reykjavik', 'Dubrovnik', 'Athens', 'Tallinn', 'Munich']
    durations = [4, 3, 4, 4, 4, 5, 2, 5, 3]
    name_to_index = {name: idx for idx, name in enumerate(city_names)}
    
    connections_str = "Copenhagen and Athens, Copenhagen and Dubrovnik, Munich and Tallinn, Copenhagen and Munich, Venice and Munich, from Reykjavik to Athens, Athens and Dubrovnik, Venice and Athens, Lyon and Barcelona, Copenhagen and Reykjavik, Reykjavik and Munich, Athens and Munich, Lyon and Munich, Barcelona and Reykjavik, Venice and Copenhagen, Barcelona and Dubrovnik, Lyon and Venice, Dubrovnik and Munich, Barcelona and Athens, Copenhagen and Barcelona, Venice and Barcelona, Barcelona and Munich, Barcelona and Tallinn, Copenhagen and Tallinn"
    connections_list = connections_str.split(', ')
    edges_set = set()
    for conn in connections_list:
        if conn.startswith('from'):
            parts = conn.split()
            a_name = parts[1]
            b_name = parts[3]
        else:
            parts = conn.split(' and ')
            a_name = parts[0]
            b_name = parts[1]
        a_idx = name_to_index[a_name]
        b_idx = name_to_index[b_name]
        edge = (min(a_idx, b_idx), max(a_idx, b_idx))
        edges_set.add(edge)
    
    s = Solver()
    
    order = [Int(f'order_{i}') for i in range(9)]
    for i in range(9):
        s.add(order[i] >= 0, order[i] < 9)
    s.add(Distinct(order))
    
    durations_arr = Array('durations_arr', IntSort(), IntSort())
    for i, d in enumerate(durations):
        s.add(durations_arr[i] == d)
    
    start_arr = Array('start_arr', IntSort(), IntSort())
    
    s.add(start_arr[order[0]] == 1)
    
    for i in range(8):
        current_city = order[i]
        next_city = order[i+1]
        s.add(start_arr[next_city] == start_arr[current_city] + durations_arr[current_city] - 1)
    
    for i in range(9):
        s.add(start_arr[i] >= 1)
        s.add(start_arr[i] + durations_arr[i] - 1 <= 26)
    
    barcelona_idx = name_to_index['Barcelona']
    s.add(And(
        start_arr[barcelona_idx] <= 12,
        start_arr[barcelona_idx] + durations_arr[barcelona_idx] - 1 >= 8
    ))
    
    copenhagen_idx = name_to_index['Copenhagen']
    s.add(And(
        start_arr[copenhagen_idx] <= 10,
        start_arr[copenhagen_idx] + durations_arr[copenhagen_idx] - 1 >= 4
    ))
    
    dubrovnik_idx = name_to_index['Dubrovnik']
    s.add(And(
        start_arr[dubrovnik_idx] <= 20,
        start_arr[dubrovnik_idx] + durations_arr[dubrovnik_idx] - 1 >= 12
    ))
    
    for i in range(8):
        c1 = order[i]
        c2 = order[i+1]
        cond = False
        for edge in edges_set:
            a, b = edge
            cond = Or(cond, And(c1 == a, c2 == b), And(c1 == b, c2 == a))
        s.add(cond)
    
    if s.check() == sat:
        m = s.model()
        order_list = [m[order[i]].as_long() for i in range(9)]
        
        start_vals = [m.evaluate(start_arr[i]).as_long() for i in range(9)]
        
        itinerary_ranges = []
        for idx, city_idx in enumerate(order_list):
            city_name = city_names[city_idx]
            start_day = start_vals[city_idx]
            if idx < 8:
                end_day = start_day + durations[city_idx] - 2
            else:
                end_day = start_day + durations[city_idx] - 1
            
            if start_day == end_day:
                day_range_str = f"Day {start_day}"
            else:
                day_range_str = f"Day {start_day}-{end_day}"
            
            itinerary_ranges.append({'day_range': day_range_str, 'place': city_name})
        
        result = {"itinerary": itinerary_ranges}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
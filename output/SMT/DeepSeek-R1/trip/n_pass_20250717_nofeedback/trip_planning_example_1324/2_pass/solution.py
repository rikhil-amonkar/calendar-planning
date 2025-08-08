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
    
    cumulative = [Int(f'cumulative_{i}') for i in range(9)]
    s.add(cumulative[0] == 1)
    for i in range(1, 9):
        prev_duration = durations_arr[order[i-1]] - 1
        s.add(cumulative[i] == cumulative[i-1] + prev_duration)
    
    s.add(cumulative[8] + durations_arr[order[8]] - 1 <= 26)
    
    barcelona_idx = name_to_index['Barcelona']
    s.add(Or([And(order[i] == barcelona_idx, cumulative[i] >= 8, cumulative[i] <= 12) for i in range(9)]))
    
    copenhagen_idx = name_to_index['Copenhagen']
    s.add(Or([And(order[i] == copenhagen_idx, cumulative[i] >= 4, cumulative[i] <= 10) for i in range(9)]))
    
    dubrovnik_idx = name_to_index['Dubrovnik']
    s.add(Or([And(order[i] == dubrovnik_idx, cumulative[i] >= 12, cumulative[i] <= 20) for i in range(9)]))
    
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
        cumulative_list = [m[cumulative[i]].as_long() for i in range(9)]
        
        start_days = [0] * 9
        for pos in range(9):
            city_idx = order_list[pos]
            start_days[city_idx] = cumulative_list[pos]
        
        itinerary = []
        for day in range(1, 27):
            cities_today = []
            for city_idx in range(9):
                start = start_days[city_idx]
                end = start + durations[city_idx] - 1
                if start <= day <= end:
                    cities_today.append(city_names[city_idx])
            for city in cities_today:
                itinerary.append({"day": day, "place": city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
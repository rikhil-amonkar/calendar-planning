from z3 import *
import json

def main():
    cities = ["Helsinki", "Warsaw", "Madrid", "Split", "Reykjavik", "Budapest"]
    dur = [2, 3, 4, 4, 2, 4]
    
    edges = [
        (0,4), (4,0),  # Helsinki <-> Reykjavik
        (5,1), (1,5),  # Budapest <-> Warsaw
        (2,3), (3,2),  # Madrid <-> Split
        (0,3), (3,0),  # Helsinki <-> Split
        (0,2), (2,0),  # Helsinki <-> Madrid
        (0,5), (5,0),  # Helsinki <-> Budapest
        (4,1), (1,4),  # Reykjavik <-> Warsaw
        (0,1), (1,0),  # Helsinki <-> Warsaw
        (2,5), (5,2),  # Madrid <-> Budapest
        (4,5), (5,4),  # Budapest <-> Reykjavik
        (2,1), (1,2),  # Madrid <-> Warsaw
        (1,3), (3,1),  # Warsaw <-> Split
        (4,2)          # Reykjavik -> Madrid
    ]
    
    s = Solver()
    order = [Int(f'order_{i}') for i in range(6)]
    
    for i in range(6):
        s.add(order[i] >= 0, order[i] < 6)
    
    s.add(Distinct(order))
    
    for i in range(5):
        constraints = []
        for a, b in edges:
            constraints.append(And(order[i] == a, order[i+1] == b))
        s.add(Or(constraints))
    
    def city_dur(city):
        res = dur[5]
        for idx in [4,3,2,1,0]:
            res = If(city == idx, dur[idx], res)
        return res
    
    prefix_arr = [Int(f'prefix_{i}') for i in range(6)]
    s.add(prefix_arr[0] == 0)
    for i in range(1, 6):
        s.add(prefix_arr[i] == prefix_arr[i-1] + (city_dur(order[i-1]) - 1))
    
    s_hel = Int('s_hel')
    s_war = Int('s_war')
    s_rey = Int('s_rey')
    
    hel_expr = Int('hel_expr')
    war_expr = Int('war_expr')
    rey_expr = Int('rey_expr')
    
    for k in range(6):
        s.add(If(order[k] == 0, hel_expr == 1 + prefix_arr[k], True))
        s.add(If(order[k] == 1, war_expr == 1 + prefix_arr[k], True))
        s.add(If(order[k] == 4, rey_expr == 1 + prefix_arr[k], True))
    
    s.add(s_hel == hel_expr)
    s.add(s_war == war_expr)
    s.add(s_rey == rey_expr)
    
    s.add(s_hel <= 2)
    s.add(And(s_war >= 7, s_war <= 11))
    s.add(And(s_rey >= 7, s_rey <= 9))
    
    if s.check() == sat:
        m = s.model()
        order_model = [m.evaluate(order[i]).as_long() for i in range(6)]
        
        start_days = [1]
        for i in range(1, 6):
            start_days.append(start_days[i-1] + dur[order_model[i-1]] - 1)
        
        itinerary_list = []
        for i in range(6):
            city_idx = order_model[i]
            start = start_days[i]
            for j in range(dur[city_idx]):
                day = start + j
                itinerary_list.append({"day": day, "place": cities[city_idx]})
        
        result_dict = {"itinerary": itinerary_list}
        print(json.dumps(result_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
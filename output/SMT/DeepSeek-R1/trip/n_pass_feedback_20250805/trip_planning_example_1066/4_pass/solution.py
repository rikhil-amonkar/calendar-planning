from z3 import *
import json

def main():
    city_ids = {
        'Brussels': 0,
        'Bucharest': 1,
        'Stuttgart': 2,
        'Mykonos': 3,
        'Helsinki': 4,
        'Split': 5,
        'London': 6,
        'Madrid': 7
    }
    
    flight_list = [
        "Helsinki and London",
        "Split and Madrid",
        "Helsinki and Madrid",
        "London and Madrid",
        "Brussels and London",
        "Bucharest and London",
        "Brussels and Bucharest",
        "Bucharest and Madrid",
        "Split and Helsinki",
        "Mykonos and Madrid",
        "Stuttgart and London",
        "Helsinki and Brussels",
        "Brussels and Madrid",
        "Split and London",
        "Stuttgart and Split",
        "London and Mykonos"
    ]
    
    allowed_set = set()
    for flight in flight_list:
        parts = flight.split(' and ')
        city1 = parts[0]
        city2 = parts[1]
        id1 = city_ids[city1]
        id2 = city_ids[city2]
        if id1 < id2:
            allowed_set.add((id1, id2))
        else:
            allowed_set.add((id2, id1))
    allowed_pairs = list(allowed_set)
    
    cities_7 = ['Brussels', 'Bucharest', 'Stuttgart', 'Mykonos', 'Helsinki', 'Split', 'London']
    durs = [4, 3, 4, 2, 5, 3, 5]
    
    s = Solver()
    
    order = [Int(f'order_{i}') for i in range(7)]
    for i in range(7):
        s.add(order[i] >= 0, order[i] <= 6)
    s.add(Distinct(order))
    
    start = [Int(f'start_{i}') for i in range(7)]
    end = [Int(f'end_{i}') for i in range(7)]
    
    dur_arr = Array('dur_arr', IntSort(), IntSort())
    for idx, dur_val in enumerate(durs):
        s.add(dur_arr[idx] == dur_val)
    
    s.add(start[0] == 1)
    s.add(end[0] == start[0] + dur_arr[order[0]] - 1)
    
    for i in range(1, 7):
        s.add(start[i] == end[i-1])
        s.add(end[i] == start[i] + dur_arr[order[i]] - 1)
    
    s.add(end[6] == 20)
    
    stuttgart_constraint = []
    for i in range(7):
        stuttgart_constraint.append(And(order[i] == city_ids['Stuttgart'], start[i] <= 4))
    s.add(Or(stuttgart_constraint))
    
    for i in range(6):
        a = order[i]
        b = order[i+1]
        conds = []
        for pair in allowed_pairs:
            conds.append(Or(And(a == pair[0], b == pair[1]), And(a == pair[1], b == pair[0])))
        s.add(Or(conds))
    
    last_city = order[6]
    madrid_id = city_ids['Madrid']
    mad_conds = []
    for pair in allowed_pairs:
        mad_conds.append(Or(And(last_city == pair[0], madrid_id == pair[1]), And(last_city == pair[1], madrid_id == pair[0])))
    s.add(Or(mad_conds))
    
    if s.check() == sat:
        model = s.model()
        order_vals = [model.evaluate(order[i]).as_long() for i in range(7)]
        start_vals = [model.evaluate(start[i]).as_long() for i in range(7)]
        end_vals = [model.evaluate(end[i]).as_long() for i in range(7)]
        
        city_id_to_name = {
            0: 'Brussels',
            1: 'Bucharest',
            2: 'Stuttgart',
            3: 'Mykonos',
            4: 'Helsinki',
            5: 'Split',
            6: 'London'
        }
        
        itinerary = []
        for i in range(7):
            city_id = order_vals[i]
            city_name = city_id_to_name[city_id]
            day_range = f"Day {start_vals[i]}-{end_vals[i]}"
            itinerary.append({'day_range': day_range, 'place': city_name})
        
        itinerary.append({'day_range': 'Day 20-21', 'place': 'Madrid'})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
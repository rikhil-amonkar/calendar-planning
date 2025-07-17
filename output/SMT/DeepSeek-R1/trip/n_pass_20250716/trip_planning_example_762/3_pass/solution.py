from z3 import *
import json

def main():
    cities = ["Dublin", "Madrid", "Oslo", "London", "Vilnius", "Berlin"]
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    days_req = [3, 2, 3, 2, 3, 5]
    events = {
        city_to_index["Dublin"]: (7, 9),
        city_to_index["Madrid"]: (2, 3),
        city_to_index["Berlin"]: (3, 7)
    }
    flights_list = [
        (city_to_index["London"], city_to_index["Madrid"]),
        (city_to_index["Oslo"], city_to_index["Vilnius"]),
        (city_to_index["Berlin"], city_to_index["Vilnius"]),
        (city_to_index["Madrid"], city_to_index["Oslo"]),
        (city_to_index["Madrid"], city_to_index["Dublin"]),
        (city_to_index["London"], city_to_index["Oslo"]),
        (city_to_index["Madrid"], city_to_index["Berlin"]),
        (city_to_index["Berlin"], city_to_index["Oslo"]),
        (city_to_index["Dublin"], city_to_index["Oslo"]),
        (city_to_index["London"], city_to_index["Dublin"]),
        (city_to_index["London"], city_to_index["Berlin"]),
        (city_to_index["Berlin"], city_to_index["Dublin"])
    ]
    directed_edges = []
    for a, b in flights_list:
        directed_edges.append((a, b))
        directed_edges.append((b, a))
    
    C = [Int(f'C_{i}') for i in range(6)]
    s = Solver()
    
    for i in range(6):
        s.add(And(C[i] >= 0, C[i] < 6))
    s.add(Distinct(C))
    
    days_req_arr = Array('days_req_arr', IntSort(), IntSort())
    for i in range(6):
        days_req_arr = Store(days_req_arr, i, days_req[i])
    
    base_i_list = [IntVal(0)]
    start_i_list = []
    end_i_list = []
    
    for i in range(6):
        start_i = base_i_list[i] + 1
        end_i = base_i_list[i] + Select(days_req_arr, C[i])
        start_i_list.append(start_i)
        end_i_list.append(end_i)
        if i < 5:
            next_base = base_i_list[i] + (Select(days_req_arr, C[i]) - 1)
            base_i_list.append(next_base)
    
    s.add(end_i_list[5] == 13)
    
    for city_idx, (e_start, e_end) in events.items():
        or_conditions = []
        for i in range(6):
            cond = And(C[i] == city_idx, start_i_list[i] <= e_end, end_i_list[i] >= e_start)
            or_conditions.append(cond)
        s.add(Or(or_conditions))
    
    for i in range(5):
        cons_list = []
        for a, b in directed_edges:
            cons_list.append(And(C[i] == a, C[i+1] == b))
        s.add(Or(cons_list))
    
    if s.check() == sat:
        m = s.model()
        perm = [m.evaluate(C[i]).as_long() for i in range(6)]
        city_sequence = [cities[idx] for idx in perm]
        
        start_days = []
        end_days = []
        base_val = 0
        for i in range(6):
            city_idx = perm[i]
            if i == 0:
                start_day = 1
            else:
                start_day = base_val + 1
            end_day = start_day + days_req[city_idx] - 1
            base_val = base_val + (days_req[city_idx] - 1)
            start_days.append(start_day)
            end_days.append(end_day)
        
        itinerary = []
        for i in range(6):
            start = start_days[i]
            end = end_days[i]
            if start == end:
                day_str = f"Day {start}"
            else:
                day_str = f"Day {start}-{end}"
            itinerary.append({"day_range": day_str, "place": city_sequence[i]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()
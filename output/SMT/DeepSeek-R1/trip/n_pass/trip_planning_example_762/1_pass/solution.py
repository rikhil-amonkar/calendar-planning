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
    
    cumul_expr = [days_req[C[0]]]
    for i in range(1, 6):
        cumul_expr.append(cumul_expr[i-1] + days_req[C[i]])
    
    for city_idx, (event_start, event_end) in events.items():
        constraints = []
        for pos in range(6):
            cond = (C[pos] == city_idx)
            if pos == 0:
                s0 = 1
                e0 = cumul_expr[0]
                c1 = (s0 <= event_end)
                c2 = (e0 >= event_start)
                constraints.append(And(cond, c1, c2))
            else:
                s_i = 1 + cumul_expr[pos-1] - pos
                e_i = cumul_expr[pos] - pos
                c1 = (s_i <= event_end)
                c2 = (e_i >= event_start)
                constraints.append(And(cond, c1, c2))
        s.add(Or(constraints))
    
    for i in range(5):
        cons_list = []
        for a, b in directed_edges:
            cons_list.append(And(C[i] == a, C[i+1] == b))
        s.add(Or(cons_list))
    
    if s.check() == sat:
        m = s.model()
        perm = [m.evaluate(C[i]).as_long() for i in range(6)]
        city_sequence = [cities[idx] for idx in perm]
        cumul_vals = []
        total = 0
        for idx in perm:
            total += days_req[idx]
            cumul_vals.append(total)
        
        itinerary = []
        for i in range(6):
            if i == 0:
                start = 1
            else:
                start = cumul_vals[i-1] - (i-1)
            end = cumul_vals[i] - i
            day_range = f"Day {start}-{end}" if start != end else f"Day {start}"
            itinerary.append({"day_range": day_range, "place": city_sequence[i]})
            if i < 5:
                itinerary.append({"day_range": f"Day {end}", "place": city_sequence[i]})
                itinerary.append({"day_range": f"Day {end}", "place": city_sequence[i+1]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()
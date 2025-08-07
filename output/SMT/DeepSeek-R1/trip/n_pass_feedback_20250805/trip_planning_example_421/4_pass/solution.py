from z3 import *
import json

def main():
    cities = ["Nice", "Krakow", "Dublin", "Lyon", "Frankfurt"]
    n = len(cities)
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    
    allowed_flights = [
        ("Nice", "Dublin"),
        ("Dublin", "Frankfurt"),
        ("Dublin", "Krakow"),
        ("Krakow", "Frankfurt"),
        ("Lyon", "Frankfurt"),
        ("Nice", "Frankfurt"),
        ("Lyon", "Dublin"),
        ("Nice", "Lyon")
    ]
    allowed_directed = set()
    for a, b in allowed_flights:
        a_idx = city_to_index[a]
        b_idx = city_to_index[b]
        allowed_directed.add((a_idx, b_idx))
        allowed_directed.add((b_idx, a_idx))
    
    s = Solver()
    
    block_city = [Int('bc_%d' % i) for i in range(5)]
    for i in range(5):
        s.add(block_city[i] >= 0, block_city[i] < 5)
    s.add(Distinct(block_city))
    
    s.add(block_city[0] == city_to_index["Nice"])
    s.add(block_city[4] == city_to_index["Frankfurt"])
    
    dur = [Int('dur_%d' % i) for i in range(5)]
    for i in range(5):
        s.add(dur[i] == If(block_city[i] == city_to_index["Nice"], 5,
                       If(block_city[i] == city_to_index["Krakow"], 6,
                       If(block_city[i] == city_to_index["Dublin"], 7,
                       If(block_city[i] == city_to_index["Lyon"], 4, 2)))))
    
    e0 = dur[0]
    e1 = e0 + dur[1] - 1
    e2 = e1 + dur[2] - 1
    e3 = e2 + dur[3] - 1
    s.add(e3 + dur[4] == 20)
    
    for i in range(4):
        a = block_city[i]
        b = block_city[i+1]
        constraints = []
        for (a_idx, b_idx) in allowed_directed:
            constraints.append(And(a == a_idx, b == b_idx))
        s.add(Or(constraints))
    
    if s.check() == sat:
        model = s.model()
        bc_val = [model.evaluate(block_city[i]).as_long() for i in range(5)]
        dur_val = [model.evaluate(dur[i]).as_long() for i in range(5)]
        e0_val = dur_val[0]
        e1_val = e0_val + dur_val[1] - 1
        e2_val = e1_val + dur_val[2] - 1
        e3_val = e2_val + dur_val[3] - 1
        start_days = [1, e0_val, e1_val, e2_val, e3_val]
        end_days = [e0_val, e1_val, e2_val, e3_val, 20]
        itinerary = []
        for i in range(5):
            city_name = cities[bc_val[i]]
            start = start_days[i]
            end = end_days[i]
            itinerary.append({
                'day_range': f'Day {start}-{end}',
                'place': city_name
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
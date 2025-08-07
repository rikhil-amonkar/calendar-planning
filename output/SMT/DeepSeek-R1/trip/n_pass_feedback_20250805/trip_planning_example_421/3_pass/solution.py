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
    
    s.add(block_city[4] == city_to_index["Frankfurt"])
    
    dur = [Int('dur_%d' % i) for i in range(5)]
    for i in range(5):
        s.add(dur[i] == If(block_city[i] == city_to_index["Nice"], 5,
                       If(block_city[i] == city_to_index["Krakow"], 6,
                       If(block_city[i] == city_to_index["Dublin"], 7,
                       If(block_city[i] == city_to_index["Lyon"], 4, 2)))))
    
    e1 = dur[0]
    e2 = e1 + dur[1] - 1
    e3 = e2 + dur[2] - 1
    e4 = e3 + dur[3] - 1
    
    s.add(e4 + dur[4] == 21)
    
    nice_idx = city_to_index["Nice"]
    s.add(Or(
        block_city[0] == nice_idx,
        And(block_city[1] == nice_idx, e1 <= 5),
        And(block_city[2] == nice_idx, e2 <= 5),
        And(block_city[3] == nice_idx, e3 <= 5)
    ))
    
    for i in range(4):
        a = block_city[i]
        b = block_city[i+1]
        constraints = []
        for (a_idx, b_idx) in allowed_directed:
            constraints.append(And(a == a_idx, b == b_idx))
        s.add(Or(constraints))
    
    s.add(e1 >= 1, e1 <= 20)
    s.add(e2 >= e1, e2 <= 20)
    s.add(e3 >= e2, e3 <= 20)
    s.add(e4 >= e3, e4 <= 20)
    
    if s.check() == sat:
        model = s.model()
        bc_val = [model.evaluate(block_city[i]).as_long() for i in range(5)]
        dur_val = [model.evaluate(dur[i]).as_long() for i in range(5)]
        e1_val = dur_val[0]
        e2_val = e1_val + dur_val[1] - 1
        e3_val = e2_val + dur_val[2] - 1
        e4_val = e3_val + dur_val[3] - 1
        start_days = [1, e1_val, e2_val, e3_val, e4_val]
        end_days = [e1_val, e2_val, e3_val, e4_val, 20]
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
from z3 import *
import json

def main():
    cities = ["Amsterdam", "Edinburgh", "Brussels", "Vienna", "Berlin", "Reykjavik"]
    durations = [4, 5, 5, 5, 4, 5]
    n = len(cities)
    
    ams_idx = cities.index("Amsterdam")
    edi_idx = cities.index("Edinburgh")
    bru_idx = cities.index("Brussels")
    vie_idx = cities.index("Vienna")
    ber_idx = cities.index("Berlin")
    rek_idx = cities.index("Reykjavik")
    
    edges = [
        (edi_idx, ber_idx),
        (ams_idx, ber_idx),
        (edi_idx, ams_idx),
        (vie_idx, ber_idx),
        (ber_idx, bru_idx),
        (vie_idx, rek_idx),
        (edi_idx, bru_idx),
        (vie_idx, bru_idx),
        (ams_idx, rek_idx),
        (rek_idx, bru_idx),
        (ams_idx, vie_idx),
        (rek_idx, ber_idx)
    ]
    allowed_pairs = set()
    for u, v in edges:
        allowed_pairs.add((u, v))
        allowed_pairs.add((v, u))
    
    s = Solver()
    
    order = [Int(f"order_{i}") for i in range(n)]
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    s.add(Distinct(order))
    
    start_day = [Int(f"start_{i}") for i in range(n)]
    end_day = [Int(f"end_{i}") for i in range(n)]
    dur = [Int(f"dur_{i}") for i in range(n)]
    
    for i in range(n):
        s.add(dur[i] == durations[order[i]])
    
    s.add(start_day[0] == 1)
    s.add(end_day[0] == start_day[0] + dur[0] - 1)
    
    for i in range(1, n):
        s.add(start_day[i] == end_day[i-1])
        s.add(end_day[i] == start_day[i] + dur[i] - 1)
    
    s.add(end_day[n-1] == 23)
    
    for i in range(n):
        city = order[i]
        s.add(If(city == ams_idx, 
                 And(start_day[i] <= 5, end_day[i] >= 8), 
                 True))
        s.add(If(city == rek_idx, 
                 And(start_day[i] <= 12, end_day[i] >= 16), 
                 True))
        s.add(If(city == ber_idx, 
                 And(start_day[i] <= 16, end_day[i] >= 19), 
                 True))
    
    for i in range(n-1):
        from_city = order[i]
        to_city = order[i+1]
        s.add(Or([And(from_city == u, to_city == v) for (u, v) in allowed_pairs]))
    
    if s.check() == sat:
        model = s.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(n)]
        start_val = [model.evaluate(start_day[i]).as_long() for i in range(n)]
        end_val = [model.evaluate(end_day[i]).as_long() for i in range(n)]
        
        itinerary_list = []
        for i in range(n):
            city_name = cities[order_val[i]]
            for day in range(start_val[i], end_val[i] + 1):
                itinerary_list.append({"day": day, "place": city_name})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
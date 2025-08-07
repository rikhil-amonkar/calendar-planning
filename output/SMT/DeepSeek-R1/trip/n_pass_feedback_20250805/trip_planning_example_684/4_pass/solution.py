from z3 import *
import json

def main():
    cities = ["Amsterdam", "Edinburgh", "Brussels", "Vienna", "Berlin", "Reykjavik"]
    durations = [4, 5, 5, 5, 4, 5]
    n = len(cities)
    
    # City indices
    ams_idx = cities.index("Amsterdam")
    edi_idx = cities.index("Edinburgh")
    bru_idx = cities.index("Brussels")
    vie_idx = cities.index("Vienna")
    ber_idx = cities.index("Berlin")
    rek_idx = cities.index("Reykjavik")
    
    # Direct flight connections (both directions)
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
    
    # City visit order (permutation)
    order = [Int(f"order_{i}") for i in range(n)]
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    s.add(Distinct(order))
    
    # Start/end days for each city segment
    start_day = [Int(f"start_{i}") for i in range(n)]
    end_day = [Int(f"end_{i}") for i in range(n)]
    
    # Duration lookup array
    duration_arr = Array('durations', IntSort(), IntSort())
    for idx, d_val in enumerate(durations):
        s.add(duration_arr[idx] == d_val)
    
    # First city starts on day 1
    s.add(start_day[0] == 1)
    s.add(end_day[0] == start_day[0] + duration_arr[order[0]] - 1)
    
    # Subsequent cities start where previous ended
    for i in range(1, n):
        s.add(start_day[i] == end_day[i-1])
        s.add(end_day[i] == start_day[i] + duration_arr[order[i]] - 1)
    
    # Total trip must be 23 days
    s.add(end_day[n-1] == 23)
    
    # Event constraints (must cover entire event period)
    for i in range(n):
        # Amsterdam: days 5-8
        s.add(If(order[i] == ams_idx, 
                 And(start_day[i] <= 5, end_day[i] >= 8), 
                 True))
        # Reykjavik: days 12-16
        s.add(If(order[i] == rek_idx, 
                 And(start_day[i] <= 12, end_day[i] >= 16), 
                 True))
        # Berlin: days 16-19
        s.add(If(order[i] == ber_idx, 
                 And(start_day[i] <= 16, end_day[i] >= 19), 
                 True))
    
    # Flight constraints (consecutive cities must have direct flights)
    for i in range(n-1):
        from_city = order[i]
        to_city = order[i+1]
        s.add(Or([And(from_city == u, to_city == v) for u, v in allowed_pairs]))
    
    # Solve and output itinerary
    if s.check() == sat:
        model = s.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(n)]
        start_val = [model.evaluate(start_day[i]).as_long() for i in range(n)]
        end_val = [model.evaluate(end_day[i]).as_long() for i in range(n)]
        
        itinerary = []
        for i in range(n):
            city = cities[order_val[i]]
            for day in range(start_val[i], end_val[i] + 1):
                itinerary.append({"day": day, "place": city})
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
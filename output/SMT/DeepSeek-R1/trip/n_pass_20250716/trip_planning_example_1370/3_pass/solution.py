from z3 import *
import json

def main():
    cities = [
        "Santorini", 
        "Krakow", 
        "Paris", 
        "Vilnius", 
        "Munich", 
        "Geneva", 
        "Amsterdam", 
        "Budapest", 
        "Split"
    ]
    durations = [5, 5, 5, 3, 5, 2, 4, 5, 4]
    
    bidirectional_edges = [
        ("Paris", "Krakow"),
        ("Paris", "Amsterdam"),
        ("Paris", "Split"),
        ("Paris", "Geneva"),
        ("Amsterdam", "Geneva"),
        ("Munich", "Split"),
        ("Munich", "Amsterdam"),
        ("Budapest", "Amsterdam"),
        ("Split", "Geneva"),
        ("Vilnius", "Split"),
        ("Munich", "Geneva"),
        ("Munich", "Krakow"),
        ("Vilnius", "Amsterdam"),
        ("Budapest", "Paris"),
        ("Krakow", "Amsterdam"),
        ("Vilnius", "Paris"),
        ("Budapest", "Geneva"),
        ("Split", "Amsterdam"),
        ("Santorini", "Geneva"),
        ("Amsterdam", "Santorini"),
        ("Munich", "Budapest"),
        ("Munich", "Paris")
    ]
    unidirectional_edges = [
        ("Vilnius", "Munich"),
        ("Krakow", "Vilnius")
    ]
    
    allowed_edges = set()
    for (a, b) in bidirectional_edges:
        try:
            ia = cities.index(a)
            ib = cities.index(b)
            allowed_edges.add((ia, ib))
            allowed_edges.add((ib, ia))
        except:
            continue
            
    for (a, b) in unidirectional_edges:
        try:
            ia = cities.index(a)
            ib = cities.index(b)
            allowed_edges.add((ia, ib))
        except:
            continue

    s = Solver()

    n = 9
    pos = [Int('pos_%d' % i) for i in range(n)]
    start = [Int('s_%d' % i) for i in range(n)]
    end = [Int('e_%d' % i) for i in range(n)]
    
    dur = [durations[i] for i in range(n)]
    dur_arr = Array('durations', IntSort(), IntSort())
    for i in range(n):
        dur_arr = Store(dur_arr, i, dur[i])
    
    for i in range(n):
        s.add(pos[i] >= 0, pos[i] < n)
    s.add(Distinct(pos))
    
    s.add(start[0] == 1)
    s.add(end[0] == start[0] + (dur_arr[pos[0]] - 1))
    
    for i in range(1, n):
        s.add(start[i] == end[i-1])
        s.add(end[i] == start[i] + (dur_arr[pos[i]] - 1))
    
    santorini_idx = cities.index("Santorini")
    krakow_idx = cities.index("Krakow")
    paris_idx = cities.index("Paris")
    geneva_idx = cities.index("Geneva")
    
    for i in range(n):
        s.add(If(pos[i] == santorini_idx, 
                 And(start[i] <= 25, end[i] >= 29), 
                 True))
        s.add(If(pos[i] == krakow_idx, 
                 And(start[i] <= 18, end[i] >= 22), 
                 True))
        s.add(If(pos[i] == paris_idx, 
                 And(start[i] <= 11, end[i] >= 15), 
                 True))
    
    flight_cons = []
    for i in range(n-1):
        flight_cons.append(Or([And(pos[i] == a, pos[i+1] == b) for (a, b) in allowed_edges]))
    s.add(flight_cons)
    
    if s.check() == sat:
        m = s.model()
        seq = [m.evaluate(pos[i]).as_long() for i in range(n)]
        s_val = [m.evaluate(start[i]).as_long() for i in range(n)]
        e_val = [m.evaluate(end[i]).as_long() for i in range(n)]
        
        itinerary = []
        for i in range(n):
            city_idx = seq[i]
            city_name = cities[city_idx]
            st = s_val[i]
            en = e_val[i]
            if st == en:
                day_range_str = f"Day {st}"
            else:
                day_range_str = f"Day {st}-{en}"
            itinerary.append({"day_range": day_range_str, "place": city_name})
            
            if i < n-1:
                itinerary.append({"day_range": f"Day {en}", "place": city_name})
                next_city_idx = seq[i+1]
                next_city_name = cities[next_city_idx]
                itinerary.append({"day_range": f"Day {en}", "place": next_city_name})
                
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()
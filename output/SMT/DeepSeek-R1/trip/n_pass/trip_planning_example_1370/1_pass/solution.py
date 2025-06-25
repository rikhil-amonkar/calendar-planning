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

    pos = [Int('pos_%d' % i) for i in range(9)]
    s = [Int('s_%d' % i) for i in range(9)]
    e = [Int('e_%d' % i) for i in range(9)]
    
    dur_arr = Array('durations', IntSort(), IntSort())
    for i in range(9):
        dur_arr = Store(dur_arr, i, durations[i])
    
    solver = Solver()
    
    for i in range(9):
        solver.add(And(pos[i] >= 0, pos[i] < 9))
    solver.add(Distinct(pos))
    
    solver.add(s[0] == 1)
    solver.add(e[0] == s[0] + (dur_arr[pos[0]] - 1))
    
    for i in range(1, 9):
        solver.add(s[i] == e[i-1])
        solver.add(e[i] == s[i] + (dur_arr[pos[i]] - 1))
    
    santorini_index = cities.index("Santorini")
    krakow_index = cities.index("Krakow")
    paris_index = cities.index("Paris")
    
    santorini_constraint = Or([And(pos[i] == santorini_index, s[i] <= 29, e[i] >= 25) for i in range(9)])
    solver.add(santorini_constraint)
    
    krakow_constraint = Or([And(pos[i] == krakow_index, s[i] <= 22, e[i] >= 18) for i in range(9)])
    solver.add(krakow_constraint)
    
    paris_constraint = Or([And(pos[i] == paris_index, s[i] <= 15, e[i] >= 11) for i in range(9)])
    solver.add(paris_constraint)
    
    for i in range(8):
        edge_constraint = Or([And(pos[i] == a, pos[i+1] == b) for (a, b) in allowed_edges])
        solver.add(edge_constraint)
    
    if solver.check() == sat:
        m = solver.model()
        seq = [m.evaluate(pos[i]).as_long() for i in range(9)]
        s_val = [m.evaluate(s[i]).as_long() for i in range(9)]
        e_val = [m.evaluate(e[i]).as_long() for i in range(9)]
        
        itinerary = []
        for i in range(9):
            city_idx = seq[i]
            city_name = cities[city_idx]
            start = s_val[i]
            end = e_val[i]
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range_str, "place": city_name})
            
            if i < 8:
                itinerary.append({"day_range": f"Day {end}", "place": city_name})
                next_city_idx = seq[i+1]
                next_city_name = cities[next_city_idx]
                itinerary.append({"day_range": f"Day {end}", "place": next_city_name})
                
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()
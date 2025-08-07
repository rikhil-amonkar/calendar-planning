from z3 import *
import json

def main():
    cities = ["Mykonos", "Nice", "Prague", "Riga", "Valencia", "Zurich", "Bucharest"]
    days_req = [3, 2, 3, 5, 5, 5, 5]
    
    edges_orig = [
        (0, 1), (0, 5),
        (2, 6), (4, 6), (5, 2),
        (3, 1), (5, 3), (5, 6), (5, 4),
        (6, 3), (2, 3), (2, 4), (5, 1)
    ]
    
    directed_edges = []
    for (a, b) in edges_orig:
        directed_edges.append((a, b))
        directed_edges.append((b, a))
    
    s = Solver()
    order = IntVector('o', 7)
    starts = IntVector('s', 7)
    
    for i in range(7):
        s.add(And(order[i] >= 0, order[i] < 7))
    s.add(Distinct(order))
    
    days_arr = []
    for i in range(7):
        d = If(order[i] == 0, 3,
              If(order[i] == 1, 2,
              If(order[i] == 2, 3,
              If(order[i] == 3, 5,
              If(order[i] == 4, 5,
              If(order[i] == 5, 5, 5))))))
        days_arr.append(d)
    
    s.add(starts[0] == 1)
    for i in range(1, 7):
        s.add(starts[i] == starts[i-1] + days_arr[i-1] - 1)
    s.add(starts[6] + days_arr[6] - 1 == 22)
    
    s.add(order[0] == 0)
    s.add(Or([And(order[i] == 2, starts[i] == 7) for i in range(7)]))
    
    for i in range(6):
        a = order[i]
        b = order[i+1]
        constraints = []
        for (x, y) in directed_edges:
            constraints.append(And(a == x, b == y))
        s.add(Or(constraints))
    
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(7)]
        starts_val = [m.evaluate(starts[i]).as_long() for i in range(7)]
        
        itinerary = []
        for i in range(7):
            city_idx = order_val[i]
            start_day = starts_val[i]
            end_day = start_day + days_req[city_idx] - 1
            day_range = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}"
            itinerary.append({"day_range": day_range, "place": cities[city_idx]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
#!/usr/bin/env python3
import json
from z3 import *

def main():
    num_segments = 8
    city_names = {
        0: "Dublin",
        1: "Krakow",
        2: "Istanbul",
        3: "Venice",
        4: "Naples",
        5: "Brussels",
        6: "Mykonos",
        7: "Frankfurt"
    }
    durations_const = {
        0: 5,
        1: 4,
        2: 3,
        3: 3,
        4: 4,
        5: 2,
        6: 4,
        7: 3
    }
    
    solver = Solver()

    order = [Int(f"order_{i}") for i in range(num_segments)]
    s_vars = [Int(f"s_{i}") for i in range(num_segments)]
    e_vars = [Int(f"e_{i}") for i in range(num_segments)]
    
    for i in range(num_segments):
        solver.add(order[i] >= 0, order[i] < num_segments)
    solver.add(Distinct(order))
    
    def duration(i):
        return If(order[i] == 0, durations_const[0],
               If(order[i] == 1, durations_const[1],
               If(order[i] == 2, durations_const[2],
               If(order[i] == 3, durations_const[3],
               If(order[i] == 4, durations_const[4],
               If(order[i] == 5, durations_const[5],
               If(order[i] == 6, durations_const[6],
               If(order[i] == 7, durations_const[7], 0))))))))
    
    solver.add(s_vars[0] == 1)
    solver.add(e_vars[0] == s_vars[0] + duration(0) - 1)
    for i in range(1, num_segments):
        solver.add(s_vars[i] == e_vars[i-1])
        solver.add(e_vars[i] == s_vars[i] + duration(i) - 1)
    solver.add(e_vars[num_segments - 1] == 21)
    
    for i in range(num_segments):
        solver.add(Implies(order[i] == 0, And(s_vars[i] == 11, e_vars[i] == 15)))
        
    for i in range(num_segments):
        solver.add(Implies(order[i] == 2, And(s_vars[i] <= 11, e_vars[i] >= 9)))
    
    for i in range(num_segments):
        solver.add(Implies(order[i] == 6, s_vars[i] <= 4))
    
    for i in range(num_segments):
        solver.add(Implies(order[i] == 7, And(s_vars[i] <= 17, e_vars[i] >= 15)))
    
    def allowed_flight(c1, c2):
        return Or(
            And(c1 == 0, c2 == 5), And(c1 == 5, c2 == 0),
            And(c1 == 6, c2 == 4), And(c1 == 4, c2 == 6),
            And(c1 == 3, c2 == 2), And(c1 == 2, c2 == 3),
            And(c1 == 7, c2 == 1), And(c1 == 1, c2 == 7),
            And(c1 == 4, c2 == 0), And(c1 == 0, c2 == 4),
            And(c1 == 1, c2 == 5), And(c1 == 5, c2 == 1),
            And(c1 == 4, c2 == 2), And(c1 == 2, c2 == 4),
            And(c1 == 4, c2 == 5), And(c1 == 5, c2 == 4),
            And(c1 == 2, c2 == 7), And(c1 == 7, c2 == 2),
            And(c1 == 5, c2 == 7), And(c1 == 7, c2 == 5),
            And(c1 == 2, c2 == 1), And(c1 == 1, c2 == 2),
            And(c1 == 2, c2 == 5), And(c1 == 5, c2 == 2),
            And(c1 == 3, c2 == 7), And(c1 == 7, c2 == 3),
            And(c1 == 4, c2 == 7), And(c1 == 7, c2 == 4),
            And(c1 == 0, c2 == 1), And(c1 == 1, c2 == 0),
            And(c1 == 3, c2 == 5), And(c1 == 5, c2 == 3),
            And(c1 == 2, c2 == 0), And(c1 == 0, c2 == 2),
            And(c1 == 3, c2 == 0), And(c1 == 0, c2 == 3),
            And(c1 == 0, c2 == 7), And(c1 == 7, c2 == 0)
        )
    
    for i in range(num_segments - 1):
        solver.add(allowed_flight(order[i], order[i+1]))
    
    if solver.check() == sat:
        m = solver.model()
        itinerary = []
        seg_order = [m.evaluate(order[i]).as_long() for i in range(num_segments)]
        seg_start = [m.evaluate(s_vars[i]).as_long() for i in range(num_segments)]
        seg_end = [m.evaluate(e_vars[i]).as_long() for i in range(num_segments)]
        for i in range(num_segments):
            itinerary.append({
                "day_range": f"Day {seg_start[i]}-{seg_end[i]}",
                "place": city_names[seg_order[i]]
            })
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()
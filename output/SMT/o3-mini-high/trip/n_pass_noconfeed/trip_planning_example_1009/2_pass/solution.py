#!/usr/bin/env python
from z3 import *
import json

def main():
    cities = ["Riga", "Manchester", "Bucharest", "Florence", "Vienna", "Istanbul", "Reykjavik", "Stuttgart"]
    durations = [4, 5, 4, 4, 2, 2, 4, 5]
    
    n = len(cities)
    total_days = 23
    
    solver = Solver()
    
    order = [Int("order_%d" % i) for i in range(n)]
    for i in range(n):
        solver.add(And(order[i] >= 0, order[i] < n))
    solver.add(Distinct(order))
    
    starts = [Int("start_%d" % i) for i in range(n)]
    for s in starts:
        solver.add(s >= 1, s <= total_days)
    
    def duration_expr(i):
        return If(order[i] == 0, durations[0],
               If(order[i] == 1, durations[1],
               If(order[i] == 2, durations[2],
               If(order[i] == 3, durations[3],
               If(order[i] == 4, durations[4],
               If(order[i] == 5, durations[5],
               If(order[i] == 6, durations[6],
               If(order[i] == 7, durations[7],
                  0))))))))
    
    solver.add(starts[0] == 1)
    
    for i in range(n - 1):
        solver.add(starts[i+1] == starts[i] + duration_expr(i) - 1)
    
    solver.add(starts[n - 1] + duration_expr(n - 1) - 1 == total_days)
    
    allowed_flights = [
        (2, 4), (4, 2),
        (6, 4), (4, 6),
        (1, 4), (4, 1),
        (1, 0), (0, 1),
        (0, 4), (4, 0),
        (5, 4), (4, 5),
        (4, 3), (3, 4),
        (7, 4), (4, 7),
        (0, 2), (2, 0),
        (5, 0), (0, 5),
        (7, 5), (5, 7),
        (6, 7), (7, 6),
        (5, 2), (2, 5),
        (1, 5), (5, 1),
        (1, 2), (2, 1),
        (7, 1), (1, 7)
    ]
    
    for i in range(n - 1):
        possible_flights = []
        for (a, b) in allowed_flights:
            possible_flights.append(And(order[i] == a, order[i+1] == b))
        solver.add(Or(possible_flights))
    
    for i in range(n):
        solver.add(Implies(order[i] == 2, And(starts[i] <= 19, starts[i] + 3 >= 16)))
    
    for i in range(n):
        solver.add(Implies(order[i] == 5, And(starts[i] <= 13, starts[i] + 1 >= 12)))
    
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(n):
            city_index = model[order[i]].as_long()
            start_day = model[starts[i]].as_long()
            d = durations[city_index]
            end_day = start_day + d - 1
            itinerary.append({
                "day_range": "Day {}-{}".format(start_day, end_day),
                "place": cities[city_index]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()
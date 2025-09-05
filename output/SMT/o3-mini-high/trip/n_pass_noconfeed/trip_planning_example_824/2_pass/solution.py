#!/usr/bin/env python3
from z3 import *
import json

def main():
    durations = {0: 5, 1: 3, 2: 3, 3: 5, 4: 3, 5: 4, 6: 5}
    city_names = {0: "Berlin", 1: "Split", 2: "Bucharest", 3: "Riga", 4: "Lisbon", 5: "Tallinn", 6: "Lyon"}
    segments = 7

    solver = Solver()

    city_vars = [Int(f"city_{i}") for i in range(segments)]
    start_vars = [Int(f"start_{i}") for i in range(segments)]
    end_vars = [Int(f"end_{i}") for i in range(segments)]

    for cv in city_vars:
        solver.add(And(cv >= 0, cv <= 6))
    solver.add(Distinct(city_vars))
    solver.add(city_vars[0] == 0)

    def duration(city):
        return If(city == 0, durations[0],
               If(city == 1, durations[1],
               If(city == 2, durations[2],
               If(city == 3, durations[3],
               If(city == 4, durations[4],
               If(city == 5, durations[5],
               If(city == 6, durations[6], 0)))))))

    solver.add(start_vars[0] == 1)
    for i in range(segments):
        solver.add(end_vars[i] == start_vars[i] + duration(city_vars[i]) - 1)
        if i > 0:
            solver.add(start_vars[i] == end_vars[i-1])
    solver.add(end_vars[segments - 1] == 22)

    for i in range(segments):
        solver.add(Implies(city_vars[i] == 2, And(start_vars[i] >= 11, start_vars[i] <= 15)))
        
    for i in range(segments):
        solver.add(Implies(city_vars[i] == 6, And(start_vars[i] <= 11, start_vars[i] + 4 >= 7)))

    allowed_pairs = [
        (0, 4), (4, 0),
        (0, 3), (3, 0),
        (0, 1), (1, 0),
        (0, 5), (5, 0),
        (4, 2), (2, 4),
        (2, 3), (3, 2),
        (1, 6), (6, 1),
        (4, 3), (3, 4),
        (6, 4), (4, 6),
        (6, 2), (2, 6),
        (3, 5)
    ]
    
    for i in range(segments - 1):
        a = city_vars[i]
        b = city_vars[i + 1]
        flight_possible = []
        for (p, q) in allowed_pairs:
            flight_possible.append(And(a == p, b == q))
        solver.add(Or(flight_possible))

    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(segments):
            s_day = model[start_vars[i]].as_long()
            e_day = model[end_vars[i]].as_long()
            city_code = model[city_vars[i]].as_long()
            itinerary.append({
                "day_range": f"Day {s_day}-{e_day}",
                "place": city_names[city_code]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()
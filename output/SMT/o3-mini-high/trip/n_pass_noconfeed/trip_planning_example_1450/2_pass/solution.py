#!/usr/bin/env python3
from z3 import *
import json

def required_duration(city):
    return If(city == 0, 3,
           If(city == 1, 4,
           If(city == 2, 2,
           If(city == 3, 4,
           If(city == 4, 4,
           If(city == 5, 4,
           If(city == 6, 2,
           If(city == 7, 4,
           If(city == 8, 3, 6)))))))))

def main():
    solver = Solver()
    cities = ["Stockholm", "Hamburg", "Florence", "Istanbul", "Oslo", "Vilnius", "Santorini", "Munich", "Frankfurt", "Krakow"]
    n_cities = len(cities)
    order = [Int(f"order_{i}") for i in range(n_cities)]
    S = [Int(f"S_{i}") for i in range(n_cities)]
    E = [Int(f"E_{i}") for i in range(n_cities)]
    F = [Bool(f"F_{i}") for i in range(n_cities - 1)]
    
    for i in range(n_cities):
        solver.add(order[i] >= 0, order[i] < n_cities)
        solver.add(S[i] >= 1, S[i] <= 32)
        solver.add(E[i] >= 1, E[i] <= 32)
    solver.add(Distinct(order))

    for i in range(n_cities):
        solver.add(E[i] == S[i] + required_duration(order[i]) - 1)
    
    solver.add(S[0] == 1)
    
    for i in range(n_cities - 1):
        solver.add(Implies(F[i], S[i+1] == E[i]))
        solver.add(Implies(Not(F[i]), S[i+1] == E[i] + 1))
    
    solver.add(Sum([If(F[i], 1, 0) for i in range(n_cities - 1)]) == 4)
    solver.add(E[n_cities - 1] == 32)
    
    allowed_connections = [
        (4, 0), (0, 4), (9, 8), (8, 9), (9, 3), (3, 9), (7, 0), (0, 7), (1, 0), (0, 1), (9, 5), (4, 3), (3, 4), (3, 0), (0, 3), (4, 9), (9, 4), (5, 3), (3, 5), (4, 5), (5, 4), (8, 3), (3, 8), (4, 8), (8, 4), (7, 1), (1, 7), (7, 3), (3, 7), (4, 7), (7, 4), (8, 2), (2, 8), (4, 1), (1, 4), (5, 8), (8, 5), (2, 7), (9, 7), (7, 9), (1, 3), (3, 1), (8, 0), (0, 8), (0, 6), (8, 7), (7, 8), (6, 4), (9, 0), (0, 9), (5, 7), (8, 1), (1, 8)
    ]
    
    for i in range(n_cities - 1):
        allowed = []
        for (a, b) in allowed_connections:
            allowed.append(And(order[i] == a, order[i+1] == b))
        solver.add(Or(allowed))
    
    for i in range(n_cities):
        solver.add(Implies(order[i] == 9, And(S[i] <= 9, E[i] >= 5)))
    
    for i in range(n_cities):
        solver.add(Implies(order[i] == 3, And(S[i] <= 29, E[i] >= 25)))
    
    if solver.check() == sat:
        m = solver.model()
        itinerary = []
        for i in range(n_cities):
            start_day = m[S[i]].as_long()
            end_day = m[E[i]].as_long()
            city_index = m[order[i]].as_long()
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": cities[city_index]
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()
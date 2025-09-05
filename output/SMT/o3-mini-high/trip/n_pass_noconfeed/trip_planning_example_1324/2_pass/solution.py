#!/usr/bin/env python3
from z3 import *
import json

def duration_constraint(city, a, d):
    return If(city == 0, d - a + 1 == 4,
           If(city == 1, d - a + 1 == 3,
           If(city == 2, d - a + 1 == 4,
           If(city == 3, d - a + 1 == 4,
           If(city == 4, d - a + 1 == 4,
           If(city == 5, d - a + 1 == 5,
           If(city == 6, d - a + 1 == 2,
           If(city == 7, d - a + 1 == 5,
           If(city == 8, d - a + 1 == 3,
              True)))))))))

def main():
    solver = Solver()
    num_cities = 9

    route = [Int("city_%d" % i) for i in range(num_cities)]
    arrival = [Int("arrival_%d" % i) for i in range(num_cities)]
    departure = [Int("departure_%d" % i) for i in range(num_cities)]

    for i in range(num_cities):
        solver.add(route[i] >= 0, route[i] < num_cities)
    solver.add(Distinct(route))

    for i in range(num_cities):
        solver.add(duration_constraint(route[i], arrival[i], departure[i]))
        solver.add(arrival[i] >= 1)
        solver.add(departure[i] <= 26)
    
    for i in range(num_cities):
        solver.add(Implies(route[i] == 1, And(arrival[i] <= 12, departure[i] >= 10)))
    for i in range(num_cities):
        solver.add(Implies(route[i] == 2, And(arrival[i] <= 10, departure[i] >= 7)))
    for i in range(num_cities):
        solver.add(Implies(route[i] == 5, And(arrival[i] <= 20, departure[i] >= 16)))
    
    solver.add(arrival[0] == 1)
    for i in range(1, num_cities):
        solver.add(arrival[i] == departure[i-1])
    solver.add(departure[num_cities-1] == 26)

    allowed_flights = [
        (2, 6),
        (2, 5),
        (8, 7),
        (2, 8),
        (0, 8),
        (4, 6),
        (6, 5),
        (0, 6),
        (3, 1),
        (2, 4),
        (4, 8),
        (6, 8),
        (3, 8),
        (1, 4),
        (0, 2),
        (1, 5),
        (3, 0),
        (5, 8),
        (1, 6),
        (2, 1),
        (0, 1),
        (1, 8),
        (1, 7),
        (2, 7)
    ]

    for i in range(num_cities - 1):
        c1 = route[i]
        c2 = route[i+1]
        flight_possible = []
        for (a_val, b_val) in allowed_flights:
            flight_possible.append(And(c1 == a_val, c2 == b_val))
            flight_possible.append(And(c1 == b_val, c2 == a_val))
        solver.add(Or(*flight_possible))

    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        city_names = {
            0: "Venice",
            1: "Barcelona",
            2: "Copenhagen",
            3: "Lyon",
            4: "Reykjavik",
            5: "Dubrovnik",
            6: "Athens",
            7: "Tallinn",
            8: "Munich"
        }
        for i in range(num_cities):
            city_id = model[route[i]].as_long()
            start_day = model[arrival[i]].as_long()
            end_day = model[departure[i]].as_long()
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city_names[city_id]
            })
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()
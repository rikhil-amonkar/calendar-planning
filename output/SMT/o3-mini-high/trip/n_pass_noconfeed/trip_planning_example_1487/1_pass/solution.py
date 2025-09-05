#!/usr/bin/env python3
from z3 import *
import json

def main():
    # Define cities and their fixed durations (in days)
    # City indices:
    # 0: Copenhagen (5 days, friend meeting between day 11 and 15)
    # 1: Geneva (3 days)
    # 2: Mykonos (2 days, conference on day 27-28)
    # 3: Naples (4 days, relatives visit between day 5 and 8)
    # 4: Prague (2 days)
    # 5: Dubrovnik (3 days)
    # 6: Athens (4 days, workshop between day 8 and 11)
    # 7: Santorini (5 days)
    # 8: Brussels (4 days)
    # 9: Munich (5 days)
    cities = ["Copenhagen", "Geneva", "Mykonos", "Naples", "Prague", "Dubrovnik", "Athens", "Santorini", "Brussels", "Munich"]
    # Durations corresponding by index:
    # Note: total sum of durations = 5+3+2+4+2+3+4+5+4+5 = 37 days.
    # With 9 overlap days (each flight day counted twice) the overall trip covers 37-9 = 28 days.
    durations = [5, 3, 2, 4, 2, 3, 4, 5, 4, 5]
    
    # Allowed direct flights (bidirectional)
    allowed_flights = [
        (0,5), (5,0),
        (8,0), (0,8),
        (4,1), (1,4),
        (6,1), (1,6),
        (3,5), (5,3),
        (6,5), (5,6),
        (1,2), (2,1),
        (3,2), (2,3),
        (3,0), (0,3),
        (9,2), (2,9),
        (3,6), (6,3),
        (4,6), (6,4),
        (7,1), (1,7),
        (6,7), (7,6),
        (3,9), (9,3),
        (4,0), (0,4),
        (8,3), (3,8),
        (6,2), (2,6),
        (6,0), (0,6),
        (3,1), (1,3),
        (5,9), (9,5),
        (8,9), (9,8),
        (4,8), (8,4),
        (8,6), (6,8),
        (6,9), (9,6),
        (1,9), (9,1),
        (0,9), (9,0),
        (8,1), (1,8),
        (0,1), (1,0),
        (4,9), (9,4),
        (0,7), (7,0),
        (3,7), (7,3),
        (1,5), (5,1)
    ]
    
    solver = Solver()
    num_cities = 10

    # Decision variables: city_order[i] is the city index visited at the i-th segment
    city_order = [Int(f"city_order_{i}") for i in range(num_cities)]
    for c in city_order:
        solver.add(And(c >= 0, c < num_cities))
    solver.add(Distinct(city_order))
    # Force Mykonos (index 2) to appear in the last position.
    solver.add(city_order[num_cities - 1] == 2)
    
    # Variables for start and end days for each city segment.
    # The itinerary starts on day 1 and ends on day 28.
    start_days = [Int(f"start_{i}") for i in range(num_cities)]
    end_days = [Int(f"end_{i}") for i in range(num_cities)]
    solver.add(start_days[0] == 1)
    solver.add(end_days[num_cities - 1] == 28)
    
    # Helper: given a city index expression, return its fixed duration.
    def duration_for(city_expr):
        return If(city_expr == 0, 5,
               If(city_expr == 1, 3,
               If(city_expr == 2, 2,
               If(city_expr == 3, 4,
               If(city_expr == 4, 2,
               If(city_expr == 5, 3,
               If(city_expr == 6, 4,
               If(city_expr == 7, 5,
               If(city_expr == 8, 4,
               If(city_expr == 9, 5, 0))))))))))
    
    # Define end day for each segment: end = start + duration - 1.
    for i in range(num_cities):
        solver.add(end_days[i] == start_days[i] + duration_for(city_order[i]) - 1)
    
    # Consecutive segments: the start day of a segment equals the end day of the previous one.
    for i in range(1, num_cities):
        solver.add(start_days[i] == end_days[i - 1])
    
    # Flight connectivity: For every consecutive pair of cities, there must be a direct flight.
    for i in range(num_cities - 1):
        flight_constraints = []
        for (a, b) in allowed_flights:
            flight_constraints.append(And(city_order[i] == a, city_order[i+1] == b))
        solver.add(Or(flight_constraints))
    
    # Additional trip constraints:
    # 1. Copenhagen friend meeting: if in Copenhagen (0), must be in the city during some day between 11 and 15.
    #    Since duration is 5, the segment covers days start ... start+4.
    for i in range(num_cities):
        solver.add(Implies(city_order[i] == 0, And(start_days[i] <= 15, start_days[i] + 4 >= 11)))
    
    # 2. Mykonos conference: if in Mykonos (2), must cover days 27 and 28.
    #    With duration 2, that forces start day = 27 (and end = 28).
    for i in range(num_cities):
        solver.add(Implies(city_order[i] == 2, start_days[i] == 27))
    
    # 3. Naples relatives visit: if in Naples (3), must be in the city at some time between day 5 and 8.
    #    With duration 4, require start <= 8 and start+3 >= 5.
    for i in range(num_cities):
        solver.add(Implies(city_order[i] == 3, And(start_days[i] <= 8, start_days[i] + 3 >= 5)))
    
    # 4. Athens workshop: if in Athens (6), must be in the city at some time between day 8 and 11.
    #    With duration 4, require start <= 11 and start+3 >= 8.
    for i in range(num_cities):
        solver.add(Implies(city_order[i] == 6, And(start_days[i] <= 11, start_days[i] + 3 >= 8)))
    
    # Solve the SMT problem.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(num_cities):
            city_idx = model.evaluate(city_order[i]).as_long()
            day_start = model.evaluate(start_days[i]).as_long()
            day_end = model.evaluate(end_days[i]).as_long()
            itinerary.append({
                "day_range": f"Day {day_start}-{day_end}",
                "place": cities[city_idx]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        result = {"itinerary": []}
        print(json.dumps(result))

if __name__ == "__main__":
    main()
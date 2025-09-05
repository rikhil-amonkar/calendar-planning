#!/usr/bin/env python3
import json
from z3 import *

def main():
    # There are 5 cities with fixed durations:
    # 0: Split (2 days)
    # 1: Helsinki (2 days)
    # 2: Reykjavik (3 days)
    # 3: Vilnius (3 days)
    # 4: Geneva (6 days)
    cities = {0: "Split", 1: "Helsinki", 2: "Reykjavik", 3: "Vilnius", 4: "Geneva"}
    
    solver = Solver()

    # Define the order in which the cities are visited.
    # These are integer variables taking values 0..4 and all must be distinct.
    order = [Int(f"city_{i}") for i in range(5)]
    for o in order:
        solver.add(o >= 0, o <= 4)
    solver.add(Distinct(order))
    
    # Define a function that returns the required duration for a given city.
    def duration(c):
        return If(c == 0, 2,
               If(c == 1, 2,
               If(c == 2, 3,
               If(c == 3, 3,
               If(c == 4, 6, 0)))))
    
    # Time segments for each visited city.
    # start[i] and end[i] denote the start and end day for the i-th segment.
    start_vars = [Int(f"start_{i}") for i in range(5)]
    end_vars = [Int(f"end_{i}") for i in range(5)]
    
    # The trip starts on day 1.
    solver.add(start_vars[0] == 1)
    
    # For each segment, the stay lasts for exactly the fixed duration.
    # If you fly from city A to city B on the same day X, then X is counted for both.
    for i in range(5):
        solver.add(end_vars[i] == start_vars[i] + duration(order[i]) - 1)
    
    # The flights cause overlaps: The next city's start day is equal to the previous city's end day.
    for i in range(1, 5):
        solver.add(start_vars[i] == end_vars[i-1])
    
    # The total distinct days must be 12, i.e. the last segment ends on day 12.
    solver.add(end_vars[4] == 12)
    
    # Direct flight connections (bidirectional) available:
    # - Split and Helsinki
    # - Geneva and Split
    # - Geneva and Helsinki
    # - Helsinki and Reykjavik
    # - Vilnius and Helsinki
    # - Split and Vilnius
    for i in range(4):
        c1 = order[i]
        c2 = order[i+1]
        direct_flight = Or(
            And(c1 == 0, c2 == 1), And(c1 == 1, c2 == 0),   # Split <-> Helsinki
            And(c1 == 4, c2 == 0), And(c1 == 0, c2 == 4),   # Geneva <-> Split
            And(c1 == 4, c2 == 1), And(c1 == 1, c2 == 4),   # Geneva <-> Helsinki
            And(c1 == 1, c2 == 2), And(c1 == 2, c2 == 1),   # Helsinki <-> Reykjavik
            And(c1 == 3, c2 == 1), And(c1 == 1, c2 == 3),   # Vilnius <-> Helsinki
            And(c1 == 0, c2 == 3), And(c1 == 3, c2 == 0)    # Split <-> Vilnius
        )
        solver.add(direct_flight)
    
    # Wedding constraint: if visiting Reykjavik (city 2),
    # then the stay in Reykjavik (which lasts 3 days) must include at least one day between day 10 and day 12.
    for i in range(5):
        # For city 2, the segment is from start to start+3-1. It must intersect [10, 12].
        solver.add(Implies(order[i] == 2, And(start_vars[i] <= 12, start_vars[i] + 3 - 1 >= 10)))
    
    # Relatives in Vilnius: if visiting Vilnius (city 3),
    # then the stay (3 days) must include at least one day between day 7 and day 9.
    for i in range(5):
        solver.add(Implies(order[i] == 3, And(start_vars[i] <= 9, start_vars[i] + 3 - 1 >= 7)))
    
    # Check for a solution.
    if solver.check() == sat:
        m = solver.model()
        itinerary = []
        for i in range(5):
            city_code = m[order[i]].as_long()
            place = cities[city_code]
            start_day = m[start_vars[i]].as_long()
            end_day = m[end_vars[i]].as_long()
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": place
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()
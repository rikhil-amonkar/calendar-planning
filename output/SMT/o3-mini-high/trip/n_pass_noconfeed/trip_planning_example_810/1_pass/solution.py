#!/usr/bin/env python3
from z3 import *
import json

def main():
    solver = Solver()
    
    # We have 7 segments corresponding to visiting 7 cities.
    # City codes: 0: Berlin, 1: Nice, 2: Athens, 3: Stockholm, 4: Barcelona, 5: Vilnius, 6: Lyon
    num_segments = 7
    city_vars = [Int("city_%d" % i) for i in range(num_segments)]
    for v in city_vars:
        solver.add(And(v >= 0, v < 7))
    # Berlin must be the first city (and also the conference city on day 1 and day 3)
    solver.add(city_vars[0] == 0)
    solver.add(Distinct(city_vars))
    
    # Allowed direct flight connections (bidirectional)
    allowed_edges = [
        (0, 1), (1, 0),
        (0, 2), (2, 0),
        (0, 3), (3, 0),
        (0, 4), (4, 0),
        (0, 5), (5, 0),
        (1, 2), (2, 1),
        (1, 3), (3, 1),
        (1, 4), (4, 1),
        (2, 3), (3, 2),
        (2, 5), (5, 2),
        (4, 2), (2, 4),
        (4, 3), (3, 4),
        (4, 6), (6, 4),
        (6, 1), (1, 6)
    ]
    for i in range(num_segments - 1):
        a = city_vars[i]
        b = city_vars[i+1]
        solver.add(Or([And(a == edge[0], b == edge[1]) for edge in allowed_edges]))
    
    # Fixed durations for each city: 
    # Berlin: 3, Nice: 5, Athens: 5, Stockholm: 5, Barcelona: 2, Vilnius: 4, Lyon: 2.
    durations_list = [3, 5, 5, 5, 2, 4, 2]
    d_vars = [Int("d_%d" % i) for i in range(num_segments)]
    for i in range(num_segments):
        solver.add(d_vars[i] ==
                   If(city_vars[i] == 0, durations_list[0],
                   If(city_vars[i] == 1, durations_list[1],
                   If(city_vars[i] == 2, durations_list[2],
                   If(city_vars[i] == 3, durations_list[3],
                   If(city_vars[i] == 4, durations_list[4],
                   If(city_vars[i] == 5, durations_list[5],
                      durations_list[6])))))))
    
    # Compute the start day for each segment.
    # If a flight happens on day X, then both the departing and arriving cities count as 
    # being visited on day X. So segments overlap on the transition day.
    start_vars = [Int("start_%d" % i) for i in range(num_segments)]
    solver.add(start_vars[0] == 1)  # Trip starts on day 1.
    for i in range(num_segments - 1):
        # The next segment starts on the last day of the previous segment.
        solver.add(start_vars[i+1] == start_vars[i] + d_vars[i] - 1)
    # Overall, the last segment must end on day 20.
    solver.add(start_vars[num_segments - 1] + d_vars[num_segments - 1] - 1 == 20)
    
    # Event constraints:
    # 1. Berlin (city code 0) is fixed as the first segment.
    #    Berlin’s segment will span Day 1-3, covering the required conference days (Day 1 and Day 3).
    #
    # 2. Barcelona (city code 4) must include either day 3 or day 4 (workshop between day 3 and day 4)
    for i in range(num_segments):
        solver.add(Implies(city_vars[i] == 4,
                           Or(And(start_vars[i] <= 3, 3 <= start_vars[i] + d_vars[i] - 1),
                              And(start_vars[i] <= 4, 4 <= start_vars[i] + d_vars[i] - 1))))
    
    # 3. Lyon (city code 6) must include either day 4 or day 5 (wedding between day 4 and day 5)
    for i in range(num_segments):
        solver.add(Implies(city_vars[i] == 6,
                           Or(And(start_vars[i] <= 4, 4 <= start_vars[i] + d_vars[i] - 1),
                              And(start_vars[i] <= 5, 5 <= start_vars[i] + d_vars[i] - 1))))
    
    if solver.check() == sat:
        model = solver.model()
        city_order = [model.evaluate(city_vars[i]).as_long() for i in range(num_segments)]
        start_days = [model.evaluate(start_vars[i]).as_long() for i in range(num_segments)]
        durations = [model.evaluate(d_vars[i]).as_long() for i in range(num_segments)]
        city_names = {
            0: "Berlin",
            1: "Nice",
            2: "Athens",
            3: "Stockholm",
            4: "Barcelona",
            5: "Vilnius",
            6: "Lyon"
        }
        
        itinerary = []
        for i in range(num_segments):
            day_start = start_days[i]
            day_end = start_days[i] + durations[i] - 1
            itinerary.append({
                "day_range": f"Day {day_start}-{day_end}",
                "place": city_names[city_order[i]]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()
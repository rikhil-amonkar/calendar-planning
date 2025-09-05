#!/usr/bin/env python
import json
from z3 import *

def main():
    # Define city codes and names.
    # 0: Manchester, 1: Stuttgart, 2: Madrid, 3: Vienna
    city_names = ["Manchester", "Stuttgart", "Madrid", "Vienna"]
    
    # Create solver.
    solver = Solver()
    
    # Create order variables for the 4 segments.
    order = [Int(f"order_{i}") for i in range(4)]
    for i in range(4):
        solver.add(And(order[i] >= 0, order[i] <= 3))
    solver.add(Distinct(order[0], order[1], order[2], order[3]))
    
    # Create start day variables for each segment.
    start = [Int(f"start_{i}") for i in range(4)]
    
    # Define a function for the fixed duration based on city.
    def duration(city):
        return If(city == 0, 7, If(city == 1, 5, If(city == 2, 4, 2)))
    
    # The itinerary is 15 days in total with flight overlaps.
    # The total distinct days = (sum of durations) - (number of transitions) = 18 - 3 = 15.
    # We fix the start day of the first segment to day 1.
    solver.add(start[0] == 1)
    
    # Consecutive segments start on the same day the previous segment ends.
    # End day for a segment i is: start[i] + duration(order[i]) - 1.
    # For each segment i+1, start[i+1] = start[i] + duration(order[i]) - 1.
    for i in range(3):
        solver.add(start[i+1] == start[i] + duration(order[i]) - 1)
    
    # The last segment must finish on day 15.
    solver.add(start[3] + duration(order[3]) - 1 == 15)
    
    # Wedding in Manchester must be attended between day 1 and day 7.
    # If Manchester (city code 0) is visited in a segment, its stay [start, start+7-1] must intersect [1,7].
    # Since start is at least 1, we require that start <= 7 for the Manchester segment.
    for i in range(4):
        solver.add(Implies(order[i] == 0, start[i] <= 7))
    
    # Workshop in Stuttgart must be attended between day 11 and day 15.
    # Stuttgart (city code 1) has a 5-day stay: [start, start+5-1]. To have an overlap with [11,15],
    # we require start + 4 >= 11, i.e. start >= 7.
    for i in range(4):
        solver.add(Implies(order[i] == 1, start[i] >= 7))
    
    # Define allowed direct flights.
    # Allowed unordered pairs are: {Manchester,Stuttgart}, {Manchester,Madrid}, {Manchester, Vienna},
    # {Stuttgart, Vienna}, {Madrid, Vienna}.
    # Since the flights are symmetric, we enforce the connection based on the order.
    def flight_possible(x, y):
        return Or(
            And(x == 0, Or(y == 1, y == 2, y == 3)),
            And(x == 1, Or(y == 0, y == 3)),
            And(x == 2, Or(y == 0, y == 3)),
            And(x == 3, Or(y == 0, y == 1, y == 2))
        )
    
    # Add flight connectivity constraints for consecutive segments.
    for i in range(3):
        solver.add(flight_possible(order[i], order[i+1]))
    
    # Solve and build the itinerary.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(4):
            city_code = model.evaluate(order[i]).as_long()
            seg_start = model.evaluate(start[i]).as_long()
            # Determine duration based on city.
            if city_code == 0:
                dur = 7
            elif city_code == 1:
                dur = 5
            elif city_code == 2:
                dur = 4
            else:
                dur = 2
            seg_end = seg_start + dur - 1
            itinerary.append({
                "day_range": f"Day {seg_start}-{seg_end}",
                "place": city_names[city_code]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()
#!/usr/bin/env python3
import json
from z3 import *

def main():
    solver = Solver()

    # Map cities to indices:
    # 0: Dubrovnik, 1: Warsaw, 2: Stuttgart, 3: Bucharest, 4: Copenhagen
    city_names = {0: "Dubrovnik", 1: "Warsaw", 2: "Stuttgart", 3: "Bucharest", 4: "Copenhagen"}
    # Required durations in each city (the “raw” duration counts, knowing that every flight day is double‐counted)
    city_durations = {0: 5, 1: 2, 2: 7, 3: 6, 4: 3}
    
    # We will plan the itinerary in 5 segments.
    # Define variables s[0]..s[4] representing the city visited during that segment.
    s = [Int(f"s{i}") for i in range(5)]
    for i in range(5):
        solver.add(And(s[i] >= 0, s[i] <= 4))
    solver.add(Distinct(s))  # each city is visited exactly once
    
    # We also define breakpoints b[0]..b[5] for the days.
    # The trip is 19 days. The idea is that segment i runs from day b[i] to b[i+1] (inclusive).
    # Because when you fly from one city to the next on the shared day, that day counts for both segments.
    b = [Int(f"b{i}") for i in range(6)]
    solver.add(b[0] == 1)
    solver.add(b[5] == 19)
    for i in range(6):
        solver.add(And(b[i] >= 1, b[i] <= 19))
    
    # For each segment i, the inter-day relation is:
    #   b[i+1] = b[i] + (duration required in the city chosen for segment i) - 1.
    # This way the total summed durations (with overlapping flight days) equals 23,
    # and the unique trip days become 23 - 4 = 19.
    for i in range(5):
        duration_expr = If(s[i] == 0, city_durations[0],
                        If(s[i] == 1, city_durations[1],
                        If(s[i] == 2, city_durations[2],
                        If(s[i] == 3, city_durations[3],
                        If(s[i] == 4, city_durations[4], 0)))))
        solver.add(b[i+1] == b[i] + duration_expr - 1)
    
    # Allowed direct flights (assumed bidirectional):
    # Warsaw <--> Copenhagen, Stuttgart <--> Copenhagen, Warsaw <--> Stuttgart,
    # Bucharest <--> Copenhagen, Bucharest <--> Warsaw, Copenhagen <--> Dubrovnik.
    allowed_flights = [
        (1, 4), (4, 1),
        (2, 4), (4, 2),
        (1, 2), (2, 1),
        (3, 4), (4, 3),
        (3, 1), (1, 3),
        (4, 0), (0, 4)
    ]
    # For transitions between consecutive segments, ensure there is a direct flight.
    for i in range(4):
        flight_options = []
        for (a, b_val) in allowed_flights:
            flight_options.append(And(s[i] == a, s[i+1] == b_val))
        solver.add(Or(flight_options))
    
    # Conference constraint: You must be in Stuttgart (city 2) on day 7 and day 13.
    # Note that if a flight happens on that day, you are considered to be in both the departing and arriving city.
    conference_days = [7, 13]
    for d in conference_days:
        # Day d is “covered” by any segment i whose interval [b[i], b[i+1]] contains d.
        covered_by_stuttgart = []
        for i in range(5):
            covered_by_stuttgart.append(And(b[i] <= d, d <= b[i+1], s[i] == 2))
        solver.add(Or(covered_by_stuttgart))
    
    # Wedding constraint: a wedding in Bucharest (city 3) must be attended on some day between day 1 and 6.
    # Since only one segment is Bucharest, we force that the segment where s[i]==3 starts on or before day 6.
    for i in range(5):
        solver.add(Implies(s[i] == 3, b[i] <= 6))
    
    # Solve the SMT constraints.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        # Each segment i runs from b[i] to b[i+1] (inclusive).
        for i in range(5):
            start_day = model[b[i]].as_long()
            end_day = model[b[i+1]].as_long()
            city_index = model[s[i]].as_long()
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city_names[city_index]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()
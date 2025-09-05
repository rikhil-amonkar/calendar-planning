import json
from z3 import *

def main():
    s = Solver()
    
    # There are 7 cities (segments)
    num_segments = 7

    # City indices and their fixed durations:
    # 0: Venice (5 days)
    # 1: Salzburg (4 days)
    # 2: Stockholm (2 days)
    # 3: Frankfurt (4 days)
    # 4: Florence (4 days)
    # 5: Barcelona (2 days)
    # 6: Stuttgart (3 days)
    city_names = ["Venice", "Salzburg", "Stockholm", "Frankfurt", "Florence", "Barcelona", "Stuttgart"]

    # Create integer variables for the order of visit.
    order = [Int(f"order_{i}") for i in range(num_segments)]
    # Create integer variables for each segment's start and end calendar day.
    start = [Int(f"start_{i}") for i in range(num_segments)]
    end = [Int(f"end_{i}") for i in range(num_segments)]
    
    # Define a function that returns the duration based on the city (using If-then-else).
    def duration_expr(city):
        return If(city == 0, 5,
               If(city == 1, 4,
               If(city == 2, 2,
               If(city == 3, 4,
               If(city == 4, 4,
               If(city == 5, 2,
               If(city == 6, 3, 0)))))))
    
    # Constraint: The itinerary is a permutation of the 7 cities.
    # Also, due to the annual Venice show from day 1 to day 5, the first city must be Venice (index 0).
    s.add(order[0] == 0)
    for i in range(num_segments):
        s.add(And(order[i] >= 0, order[i] < 7))
    for i in range(num_segments):
        for j in range(i+1, num_segments):
            s.add(order[i] != order[j])
    
    # Timeline constraints:
    # If you fly from A to B on the same day X, that day counts for both A and B.
    # We set the start of the first segment to Day 1.
    s.add(start[0] == 1)
    for i in range(num_segments):
        d_i = duration_expr(order[i])
        s.add(end[i] == start[i] + d_i - 1)
        if i < num_segments - 1:
            # The flight day from segment i to i+1 is shared, so the next segment starts on the same day the previous segment ends.
            s.add(start[i+1] == end[i])
    # Total calendar days must equal 18.
    s.add(end[num_segments - 1] == 18)
    
    # Define allowed direct flight connections (bidirectional) between cities.
    # Each tuple represents an unordered pair of cities that have a direct flight.
    allowed_pairs = [
        (0, 5),  # Venice and Barcelona
        (5, 3),  # Barcelona and Frankfurt
        (4, 3),  # Florence and Frankfurt
        (2, 5),  # Stockholm and Barcelona
        (6, 5),  # Stuttgart and Barcelona
        (3, 1),  # Frankfurt and Salzburg
        (2, 3),  # Stockholm and Frankfurt
        (6, 2),  # Stuttgart and Stockholm
        (6, 3),  # Stuttgart and Frankfurt
        (0, 6),  # Venice and Stuttgart
        (0, 3)   # Venice and Frankfurt
    ]

    # Constraint: consecutive cities in the itinerary must be connected by a direct flight.
    for i in range(num_segments - 1):
        flight_options = []
        for (a, b) in allowed_pairs:
            flight_options.append(And(order[i] == a, order[i+1] == b))
            flight_options.append(And(order[i] == b, order[i+1] == a))
        s.add(Or(flight_options))
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(num_segments):
            seg_start = m.evaluate(start[i]).as_long()
            seg_end = m.evaluate(end[i]).as_long()
            city_idx = m.evaluate(order[i]).as_long()
            itinerary.append({
                "day_range": f"Day {seg_start}-{seg_end}",
                "place": city_names[city_idx]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()
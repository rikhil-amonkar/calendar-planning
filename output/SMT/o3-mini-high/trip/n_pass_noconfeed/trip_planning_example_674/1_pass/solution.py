from z3 import *
import json

def plan_trip():
    s = Solver()
    num_segments = 6

    # We'll represent the 6 visited cities by integers:
    # 0: Helsinki, 1: Warsaw, 2: Madrid, 3: Split, 4: Reykjavik, 5: Budapest
    city_names = {0: "Helsinki", 1: "Warsaw", 2: "Madrid", 3: "Split", 4: "Reykjavik", 5: "Budapest"}
    # Required durations for each city (in terms of calendar days counted with overlap on flight day)
    required_durations = {0: 2, 1: 3, 2: 4, 3: 4, 4: 2, 5: 4}

    # Define allowed direct flights.
    # Most flights are bidirectional except the last one which is only allowed from Reykjavik to Madrid.
    allowed_flights = [
        (0, 4), (4, 0),       # Helsinki <-> Reykjavik
        (5, 1), (1, 5),       # Budapest <-> Warsaw
        (2, 3), (3, 2),       # Madrid <-> Split
        (0, 3), (3, 0),       # Helsinki <-> Split
        (0, 2), (2, 0),       # Helsinki <-> Madrid
        (0, 5), (5, 0),       # Helsinki <-> Budapest
        (4, 1), (1, 4),       # Reykjavik <-> Warsaw
        (0, 1), (1, 0),       # Helsinki <-> Warsaw
        (2, 5), (5, 2),       # Madrid <-> Budapest
        (5, 4), (4, 5),       # Budapest <-> Reykjavik
        (2, 1), (1, 2),       # Madrid <-> Warsaw
        (1, 3), (3, 1),       # Warsaw <-> Split
        (4, 2)                # Directional: from Reykjavik to Madrid
    ]
    
    # Create arrays of Z3 variables
    cities = [Int(f"city{i}") for i in range(num_segments)]
    starts = [Int(f"start{i}") for i in range(num_segments)]
    ends   = [Int(f"end{i}") for i in range(num_segments)]
    
    # Each segment represents a visit to a city. When flying from one city to the next,
    # the flight day is shared between the two segments.
    for i in range(num_segments):
        # City domain constraint (from 0 to 5)
        s.add(cities[i] >= 0, cities[i] < 6)
        # Calendar day boundaries for the segment
        s.add(starts[i] >= 1, starts[i] <= 14)
        s.add(ends[i] >= 1, ends[i] <= 14)
        s.add(starts[i] <= ends[i])
        
        # Duration constraint:
        # The number of calendar days attributed to the city is (end - start + 1)
        s.add(ends[i] - starts[i] + 1 == If(cities[i] == 0, required_durations[0],
                                     If(cities[i] == 1, required_durations[1],
                                     If(cities[i] == 2, required_durations[2],
                                     If(cities[i] == 3, required_durations[3],
                                     If(cities[i] == 4, required_durations[4],
                                     If(cities[i] == 5, required_durations[5], -1))))))
        
        # Special time-window constraints:
        # Helsinki: must be visited during day 1 or day 2 (workshop)
        s.add(Implies(cities[i] == 0, Or(And(starts[i] <= 1, 1 <= ends[i]),
                                          And(starts[i] <= 2, 2 <= ends[i]))))
        # Warsaw: must include at least one of days 9, 10 or 11 (visit relatives)
        s.add(Implies(cities[i] == 1, Or(And(starts[i] <= 9, 9 <= ends[i]),
                                          And(starts[i] <= 10, 10 <= ends[i]),
                                          And(starts[i] <= 11, 11 <= ends[i]))))
        # Reykjavik: must include day 8 or day 9 (meeting friend)
        s.add(Implies(cities[i] == 4, Or(And(starts[i] <= 8, 8 <= ends[i]),
                                          And(starts[i] <= 9, 9 <= ends[i]))))
    
    # The itinerary covers exactly 14 calendar days.
    s.add(starts[0] == 1)
    s.add(ends[num_segments - 1] == 14)
    
    # Flight transition constraints:
    # When moving from one segment to the next, the flight occurs on the day equal to the previous segment's end.
    for i in range(num_segments - 1):
        s.add(ends[i] == starts[i+1])
    
    # Flight route constraints:
    # For every consecutive pair of segments, there must be a direct flight available.
    for i in range(num_segments - 1):
        flight_possible = []
        for (a, b) in allowed_flights:
            flight_possible.append(And(cities[i] == a, cities[i+1] == b))
        s.add(Or(flight_possible))
        
    # Each city must be visited exactly once.
    s.add(Distinct(cities))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(num_segments):
            start_day = m.evaluate(starts[i]).as_long()
            end_day = m.evaluate(ends[i]).as_long()
            c_idx = m.evaluate(cities[i]).as_long()
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city_names[c_idx]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    plan_trip()
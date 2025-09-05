from z3 import *
import json

def plan_trip():
    s = Solver()
    num_segments = 6

    city_names = {0: "Helsinki", 1: "Warsaw", 2: "Madrid", 3: "Split", 4: "Reykjavik", 5: "Budapest"}
    required_durations = {0: 2, 1: 3, 2: 4, 3: 4, 4: 2, 5: 4}

    allowed_flights = [
        (0, 4), (4, 0),
        (5, 1), (1, 5),
        (2, 3), (3, 2),
        (0, 3), (3, 0),
        (0, 2), (2, 0),
        (0, 5), (5, 0),
        (4, 1), (1, 4),
        (0, 1), (1, 0),
        (2, 5), (5, 2),
        (5, 4), (4, 5),
        (2, 1), (1, 2),
        (1, 3), (3, 1),
        (4, 2)
    ]
    
    cities = [Int(f"city{i}") for i in range(num_segments)]
    starts = [Int(f"start{i}") for i in range(num_segments)]
    ends   = [Int(f"end{i}") for i in range(num_segments)]
    
    for i in range(num_segments):
        s.add(cities[i] >= 0, cities[i] < 6)
        s.add(starts[i] >= 1, starts[i] <= 14)
        s.add(ends[i] >= 1, ends[i] <= 14)
        s.add(starts[i] <= ends[i])
        
        duration_expr = If(cities[i] == 0, required_durations[0],
                        If(cities[i] == 1, required_durations[1],
                        If(cities[i] == 2, required_durations[2],
                        If(cities[i] == 3, required_durations[3],
                        If(cities[i] == 4, required_durations[4],
                           If(cities[i] == 5, required_durations[5], -1))))))
        
        s.add(ends[i] - starts[i] + 1 == duration_expr)
        
        s.add(Implies(cities[i] == 0, Or(And(starts[i] <= 1, 1 <= ends[i]),
                                          And(starts[i] <= 2, 2 <= ends[i]))))
        s.add(Implies(cities[i] == 1, Or(And(starts[i] <= 9, 9 <= ends[i]),
                                          And(starts[i] <= 10, 10 <= ends[i]),
                                          And(starts[i] <= 11, 11 <= ends[i]))))
        s.add(Implies(cities[i] == 4, Or(And(starts[i] <= 8, 8 <= ends[i]),
                                          And(starts[i] <= 9, 9 <= ends[i]))))
    
    s.add(starts[0] == 1)
    s.add(ends[num_segments - 1] == 14)
    
    for i in range(num_segments - 1):
        s.add(ends[i] == starts[i+1])
    
    for i in range(num_segments - 1):
        flight_possible = []
        for (a, b) in allowed_flights:
            flight_possible.append(And(cities[i] == a, cities[i+1] == b))
        s.add(Or(flight_possible))
        
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
import json
from z3 import *

def main():
    # City codes:
    # 0: Vienna, 1: Stockholm, 2: Nice, 3: Split
    city_names = ["Vienna", "Stockholm", "Nice", "Split"]
    
    # Create the Z3 solver
    solver = Solver()

    # Order variables for the 4 segments (each representing one city visit);
    # They form a permutation of the four cities.
    order = [Int(f"order_{i}") for i in range(4)]
    for o in order:
        # enforce domain 0..3
        solver.add(o >= 0, o <= 3)
    solver.add(Distinct(order))
    
    # Create timeline variables for each segment: start and end days
    start_vars = [Int(f"start_{i}") for i in range(4)]
    end_vars   = [Int(f"end_{i}") for i in range(4)]
    # Trip starts on Day 1 and ends on Day 9.
    solver.add(start_vars[0] == 1)
    solver.add(end_vars[3] == 9)

    # Define duration for each city (if visited in that segment) using a piecewise expression.
    # Vienna: 2 days, Stockholm: 5 days, Nice: 2 days, Split: 3 days.
    dur_expr = []
    for i in range(4):
        d = If(order[i] == 0, 2,
             If(order[i] == 1, 5,
             If(order[i] == 2, 2,
             If(order[i] == 3, 3, 0))))
        dur_expr.append(d)
    
    # Each segment's end day is computed from its start and required duration.
    for i in range(4):
        solver.add(end_vars[i] == start_vars[i] + dur_expr[i] - 1)
        
    # For consecutive segments, the next segment starts exactly when the previous one ends.
    for i in range(1, 4):
        solver.add(start_vars[i] == end_vars[i-1])
    
    # Direct flight constraints between consecutive cities.
    # Allowed flight connections:
    # Vienna <-> Stockholm, Vienna <-> Nice, Vienna <-> Split,
    # Stockholm <-> Split, Nice <-> Stockholm.
    def allowed_flight(a, b):
        return Or(
            And(a == 0, Or(b == 1, b == 2, b == 3)),       # From Vienna (0) to any of Stockholm, Nice, Split.
            And(a == 1, Or(b == 0, b == 2, b == 3)),       # From Stockholm (1) to Vienna, Nice, Split.
            And(a == 2, Or(b == 0, b == 1)),               # From Nice (2) to Vienna or Stockholm.
            And(a == 3, Or(b == 0, b == 1))                # From Split (3) to Vienna or Stockholm.
        )
    
    for i in range(3):
        solver.add(allowed_flight(order[i], order[i+1]))
    
    # Conference in Split must be attended on Day 7 and Day 9.
    # This means that on Day 7 and Day 9, the traveler must be in Split.
    conference_day7 = Or([And(order[i] == 3, start_vars[i] <= 7, 7 <= end_vars[i]) for i in range(4)])
    conference_day9 = Or([And(order[i] == 3, start_vars[i] <= 9, 9 <= end_vars[i]) for i in range(4)])
    solver.add(conference_day7)
    solver.add(conference_day9)
    
    # Workshop in Vienna must be attended between Day 1 and Day 2.
    # So the segment where Vienna is visited must cover either Day 1 or Day 2.
    workshop = Or([And(order[i] == 0, 
                      Or(And(start_vars[i] <= 1, 1 <= end_vars[i]),
                         And(start_vars[i] <= 2, 2 <= end_vars[i]))) for i in range(4)])
    solver.add(workshop)
    
    # Solve the SMT model.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(4):
            s_val = model[start_vars[i]].as_long()
            e_val = model[end_vars[i]].as_long()
            city_val = model[order[i]].as_long()
            itinerary.append({"day_range": f"Day {s_val}-{e_val}", "place": city_names[city_val]})
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == '__main__':
    main()
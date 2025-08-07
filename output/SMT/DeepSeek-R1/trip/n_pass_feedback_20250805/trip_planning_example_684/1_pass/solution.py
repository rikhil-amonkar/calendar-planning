from z3 import *
import json

def main():
    # Cities and their durations
    cities = ["Amsterdam", "Edinburgh", "Brussels", "Vienna", "Berlin", "Reykjavik"]
    durations = [4, 5, 5, 5, 4, 5]
    n = 6

    # City indices for clarity
    amsterdam = 0
    edinburgh = 1
    brussels = 2
    vienna = 3
    berlin = 4
    reykjavik = 5

    # Direct flight edges (undirected)
    edges = [
        (edinburgh, berlin),
        (amsterdam, berlin),
        (edinburgh, amsterdam),
        (vienna, berlin),
        (berlin, brussels),
        (vienna, reykjavik),
        (edinburgh, brussels),
        (vienna, brussels),
        (amsterdam, reykjavik),
        (reykjavik, brussels),
        (amsterdam, vienna),
        (reykjavik, berlin)
    ]
    
    # Create allowed pairs (both directions)
    allowed_pairs = []
    for u, v in edges:
        allowed_pairs.append((u, v))
        allowed_pairs.append((v, u))

    # Z3 variables for the permutation of cities
    seg = [Int(f"seg_{i}") for i in range(n)]
    solver = Solver()

    # Each seg[i] must be an integer between 0 and 5
    for i in range(n):
        solver.add(seg[i] >= 0, seg[i] < n)
    
    # All cities must be distinct
    solver.add(Distinct(seg))

    # End days for each segment
    e = [Int(f"e{i}") for i in range(n)]
    # Segment 0: e0 = duration of seg[0]
    solver.add(e[0] == durations[seg[0]])
    # Subsequent segments: e[i] = e[i-1] + duration[seg[i]] - 1
    for i in range(1, n):
        solver.add(e[i] == e[i-1] + durations[seg[i]] - 1)

    # Start days for each segment
    s_days = [Int(f"s{i}") for i in range(n)]
    solver.add(s_days[0] == 1)  # First segment starts on day 1
    for i in range(1, n):
        solver.add(s_days[i] == e[i-1])  # Segment i starts where segment i-1 ends

    # Event constraints
    for i in range(n):
        # Amsterdam: must have at least one day between 5 and 8
        solver.add(If(seg[i] == amsterdam, 
                     And(s_days[i] <= 8, e[i] >= 5), 
                     True))
        # Berlin: must have at least one day between 16 and 19
        solver.add(If(seg[i] == berlin, 
                     And(s_days[i] <= 19, e[i] >= 16), 
                     True))
        # Reykjavik: must have at least one day between 12 and 16
        solver.add(If(seg[i] == reykjavik, 
                     And(s_days[i] <= 16, e[i] >= 12), 
                     True))

    # Flight constraints: consecutive cities must have a direct flight
    for i in range(n-1):
        # Check if (seg[i], seg[i+1]) is in allowed_pairs
        constraints = []
        for u, v in allowed_pairs:
            constraints.append(And(seg[i] == u, seg[i+1] == v))
        solver.add(Or(constraints))

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        seg_val = [model.evaluate(seg[i]).as_long() for i in range(n)]
        s_val = [model.evaluate(s_days[i]).as_long() for i in range(n)]
        e_val = [model.evaluate(e[i]).as_long() for i in range(n)]

        # Build itinerary
        itinerary = []
        for i in range(n):
            city_name = cities[seg_val[i]]
            start = s_val[i]
            end = e_val[i]
            for day in range(start, end + 1):
                itinerary.append({"day": day, "place": city_name})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
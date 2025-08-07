from z3 import *
import json

def main():
    # Cities and their durations
    cities = ["Amsterdam", "Edinburgh", "Brussels", "Vienna", "Berlin", "Reykjavik"]
    durations = [4, 5, 5, 5, 4, 5]
    n = 6

    # City indices
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
    
    # Allowed flight pairs (both directions)
    allowed_pairs = []
    for u, v in edges:
        allowed_pairs.append((u, v))
        allowed_pairs.append((v, u))

    # Z3 solver
    solver = Solver()

    # Permutation of cities (order of visit)
    seg = [Int(f"seg_{i}") for i in range(n)]
    for i in range(n):
        solver.add(seg[i] >= 0, seg[i] < n)
    solver.add(Distinct(seg))

    # Duration array as a Z3 array
    duration_arr = Array('durations', IntSort(), IntSort())
    for idx, d_val in enumerate(durations):
        solver.add(duration_arr[idx] == d_val)

    # Durations for each segment
    d_seg = [Int(f"d_seg_{i}") for i in range(n)]
    for i in range(n):
        solver.add(d_seg[i] == duration_arr[seg[i]])

    # Start and end days for each segment
    s_days = [Int(f"s{i}") for i in range(n)]
    e_days = [Int(f"e{i}") for i in range(n)]

    # First segment starts on day 1
    solver.add(s_days[0] == 1)
    solver.add(e_days[0] == s_days[0] + d_seg[0] - 1)

    # Subsequent segments
    for i in range(1, n):
        solver.add(s_days[i] == e_days[i-1])
        solver.add(e_days[i] == s_days[i] + d_seg[i] - 1)

    # Total trip must end on day 23
    solver.add(e_days[n-1] == 23)

    # Event constraints
    for i in range(n):
        # Amsterdam: must cover at least one day between 5 and 8
        solver.add(If(seg[i] == amsterdam, 
                     And(s_days[i] <= 8, e_days[i] >= 5), 
                     True))
        # Berlin: must cover at least one day between 16 and 19
        solver.add(If(seg[i] == berlin, 
                     And(s_days[i] <= 19, e_days[i] >= 16), 
                     True))
        # Reykjavik: must cover at least one day between 12 and 16
        solver.add(If(seg[i] == reykjavik, 
                     And(s_days[i] <= 16, e_days[i] >= 12), 
                     True))

    # Flight constraints: consecutive cities must have a direct flight
    for i in range(n-1):
        constraints = []
        for u, v in allowed_pairs:
            constraints.append(And(seg[i] == u, seg[i+1] == v))
        solver.add(Or(constraints))

    # Solve and generate itinerary
    if solver.check() == sat:
        model = solver.model()
        seg_val = [model.evaluate(seg[i]).as_long() for i in range(n)]
        s_val = [model.evaluate(s_days[i]).as_long() for i in range(n)]
        e_val = [model.evaluate(e_days[i]).as_long() for i in range(n)]

        itinerary = []
        for i in range(n):
            city = cities[seg_val[i]]
            for day in range(s_val[i], e_val[i] + 1):
                itinerary.append({"day": day, "place": city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
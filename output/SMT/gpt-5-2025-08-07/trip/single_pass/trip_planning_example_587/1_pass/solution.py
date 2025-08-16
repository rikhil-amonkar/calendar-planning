import json
from z3 import *

def solve_itinerary():
    # Cities and durations
    cities = ["Manchester", "Istanbul", "Venice", "Krakow", "Lyon"]
    idx = {name: i for i, name in enumerate(cities)}

    durations = {
        idx["Manchester"]: 3,
        idx["Istanbul"]: 7,
        idx["Venice"]: 7,
        idx["Krakow"]: 6,
        idx["Lyon"]: 2,
    }

    # Undirected direct-flight edges (we'll model as bidirectional)
    undirected_edges = [
        ("Manchester", "Venice"),
        ("Manchester", "Istanbul"),
        ("Venice", "Istanbul"),
        ("Istanbul", "Krakow"),
        ("Venice", "Lyon"),
        ("Lyon", "Istanbul"),
        ("Manchester", "Krakow"),
    ]
    edges = set()
    for a, b in undirected_edges:
        ai, bi = idx[a], idx[b]
        edges.add((ai, bi))
        edges.add((bi, ai))

    # Z3 variables
    s = {c: Int(f"s_{c}") for c in range(len(cities))}  # start day
    e = {c: Int(f"e_{c}") for c in range(len(cities))}  # end day

    # next[c1,c2] means we fly from c1 to c2 on day e[c1] (shared with s[c2])
    next_vars = {(i, j): Bool(f"next_{i}_{j}") for (i, j) in edges}

    solver = Solver()

    # Domain constraints for start/end days and exact durations
    for c in range(len(cities)):
        solver.add(s[c] >= 1, s[c] <= 21)
        solver.add(e[c] >= 1, e[c] <= 21)
        solver.add(e[c] == s[c] + durations[c] - 1)

    # Each city has at most one predecessor and at most one successor (path)
    pred_counts = {}
    succ_counts = {}

    for c in range(len(cities)):
        succs = [next_vars[(c, j)] for j in range(len(cities)) if (c, j) in next_vars]
        preds = [next_vars[(i, c)] for i in range(len(cities)) if (i, c) in next_vars]
        succ_counts[c] = Sum([If(b, 1, 0) for b in succs]) if succs else IntVal(0)
        pred_counts[c] = Sum([If(b, 1, 0) for b in preds]) if preds else IntVal(0)
        solver.add(succ_counts[c] <= 1)
        solver.add(pred_counts[c] <= 1)

    # The path must use exactly 4 edges (5 cities visited once => 4 transitions)
    total_edges = Sum([If(b, 1, 0) for b in next_vars.values()])
    solver.add(total_edges == 4)

    # Temporal linking: if c1 -> c2, then s[c2] == e[c1]
    for (i, j), var in next_vars.items():
        solver.add(Implies(var, s[j] == e[i]))

    # Start city has no predecessor => starts at day 1
    for c in range(len(cities)):
        solver.add(Implies(pred_counts[c] == 0, s[c] == 1))
    # End city has no successor => ends at day 21
    for c in range(len(cities)):
        solver.add(Implies(succ_counts[c] == 0, e[c] == 21))

    # Wedding in Manchester between day 1 and day 3: Manchester must intersect [1,3]
    man = idx["Manchester"]
    solver.add(s[man] <= 3)  # with duration 3, this ensures overlap with [1,3]

    # Workshop in Venice between day 3 and day 9: Venice must intersect [3,9]
    ven = idx["Venice"]
    solver.add(s[ven] <= 9)
    solver.add(e[ven] >= 3)

    # Solve
    if solver.check() != sat:
        raise RuntimeError("No valid itinerary found.")

    model = solver.model()

    # Extract intervals
    intervals = {}
    for c in range(len(cities)):
        intervals[c] = (model[s[c]].as_long(), model[e[c]].as_long())

    # Build itinerary: for each day, list the city/cities you're in (flight days count for both)
    itinerary = []
    for day in range(1, 21 + 1):
        todays_cities = []
        for c in range(len(cities)):
            start, end = intervals[c]
            if start <= day <= end:
                todays_cities.append(cities[c])
        # Sort to keep deterministic output (optional)
        todays_cities.sort()
        itinerary.append({"day": day, "place": todays_cities})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False, indent=2))
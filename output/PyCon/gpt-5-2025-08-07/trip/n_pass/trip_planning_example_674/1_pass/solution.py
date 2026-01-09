import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and durations
    cities = ["Helsinki", "Warsaw", "Madrid", "Split", "Reykjavik", "Budapest"]
    durations = {
        "Helsinki": 2,
        "Warsaw": 3,
        "Madrid": 4,
        "Split": 4,
        "Reykjavik": 2,
        "Budapest": 4
    }

    # Build adjacency (direct flights). Undirected pairs add both directions; directed adds one way.
    undirected_edges = [
        ("Helsinki", "Reykjavik"),
        ("Budapest", "Warsaw"),
        ("Madrid", "Split"),
        ("Helsinki", "Split"),
        ("Helsinki", "Madrid"),
        ("Helsinki", "Budapest"),
        ("Reykjavik", "Warsaw"),
        ("Helsinki", "Warsaw"),
        ("Madrid", "Budapest"),
        ("Budapest", "Reykjavik"),
        ("Madrid", "Warsaw"),
        ("Warsaw", "Split"),
    ]
    directed_edges = [
        ("Reykjavik", "Madrid"),
    ]

    adjacency = {c: set() for c in cities}
    for a, b in undirected_edges:
        adjacency[a].add(b)
        adjacency[b].add(a)
    for a, b in directed_edges:
        adjacency[a].add(b)

    # Create CSP problem
    problem = Problem()

    # Variables: city at position i (P1..P6), start day (S1..S6), end day (E1..E6)
    pos_vars = [f"P{i}" for i in range(1, 7)]
    start_vars = [f"S{i}" for i in range(1, 7)]
    end_vars = [f"E{i}" for i in range(1, 7)]

    # Add variables to problem
    for v in pos_vars:
        problem.addVariable(v, cities)
    for v in start_vars + end_vars:
        problem.addVariable(v, range(1, 15))  # days 1..14 inclusive

    # All cities must be visited exactly once
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Trip timeline continuity and total length 14 days
    problem.addConstraint(lambda s: s == 1, ("S1",))
    problem.addConstraint(lambda e: e == 14, ("E6",))
    for i in range(1, 6):
        problem.addConstraint(lambda s_next, e_cur: s_next == e_cur, (f"S{i+1}", f"E{i}"))

    # Link duration to each city's start/end
    for i in range(1, 7):
        def dur_cons(pi, si, ei, durations=durations):
            return (ei - si + 1) == durations[pi]
        problem.addConstraint(dur_cons, (f"P{i}", f"S{i}", f"E{i}"))

    # Direct flight constraints between consecutive cities
    for i in range(1, 6):
        def flight_cons(a, b, adjacency=adjacency):
            return b in adjacency[a]
        problem.addConstraint(flight_cons, (f"P{i}", f"P{i+1}"))

    # Fixed city/day constraints based on events:
    # - Helsinki workshop between day 1 and day 2 (and Helsinki stay is exactly 2 days)
    problem.addConstraint(lambda p1: p1 == "Helsinki", ("P1",))
    # - Reykjavik meeting between day 8 and day 9: Reykjavik exactly on days 8-9
    for i in range(1, 7):
        def rey_cons(pi, si, ei):
            return (pi != "Reykjavik") or (si == 8 and ei == 9)
        problem.addConstraint(rey_cons, (f"P{i}", f"S{i}", f"E{i}"))
    # - Warsaw relatives between day 9 and day 11: Warsaw exactly on days 9-11
    for i in range(1, 7):
        def warsaw_cons(pi, si, ei):
            return (pi != "Warsaw") or (si == 9 and ei == 11)
        problem.addConstraint(warsaw_cons, (f"P{i}", f"S{i}", f"E{i}"))

    # Solve
    solutions = problem.getSolutions()

    itinerary = []
    if solutions:
        # Choose a solution deterministically: sort by the tuple of (P1..P6) then (S1..S6)
        def sol_key(sol):
            return tuple(sol[p] for p in pos_vars) + tuple(sol[s] for s in start_vars)
        solutions.sort(key=sol_key)
        sol = solutions[0]

        # Build itinerary list in order of positions 1..6
        for i in range(1, 7):
            s = sol[f"S{i}"]
            e = sol[f"E{i}"]
            city = sol[f"P{i}"]
            itinerary.append({"day_range": f"Day {s}-{e}", "place": city})
    else:
        # No solution found: output empty itinerary
        itinerary = []

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
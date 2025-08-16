import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = [
        "Stuttgart",
        "Istanbul",
        "Vilnius",
        "Seville",
        "Geneva",
        "Valencia",
        "Munich",
        "Reykjavik",
    ]
    idx = {c: i for i, c in enumerate(cities)}
    n_days = 25

    # Required stay durations per city
    required_days = {
        "Stuttgart": 4,
        "Istanbul": 4,
        "Vilnius": 4,
        "Seville": 3,
        "Geneva": 5,
        "Valencia": 5,
        "Munich": 3,
        "Reykjavik": 4,
    }

    # Day-specific presence constraints:
    # You have to attend a workshop in Reykjavik between day 1 and day 4.
    must_be_reyk_days = list(range(1, 5))
    # During day 4 and day 7, you have to attend a conference in Stuttgart.
    must_be_stu_days = [4, 7]
    # From day 13 to day 15, there is an annual show you want to attend in Munich.
    must_be_muc_days = list(range(13, 16))
    # Visit relatives in Istanbul between day 19 and day 22.
    must_be_ist_days = list(range(19, 23))

    # Build directed adjacency from the provided "direct flights"
    edges = set()

    def add_undirected(a, b):
        edges.add((idx[a], idx[b]))
        edges.add((idx[b], idx[a]))

    def add_direct(a, b):
        edges.add((idx[a], idx[b]))

    # Given direct flights:
    add_undirected("Geneva", "Istanbul")
    add_undirected("Reykjavik", "Munich")
    add_undirected("Stuttgart", "Valencia")
    add_direct("Reykjavik", "Stuttgart")
    add_undirected("Stuttgart", "Istanbul")
    add_undirected("Munich", "Geneva")
    add_undirected("Istanbul", "Vilnius")
    add_undirected("Valencia", "Seville")
    add_undirected("Valencia", "Istanbul")
    add_direct("Vilnius", "Munich")
    add_undirected("Seville", "Munich")
    add_undirected("Munich", "Istanbul")
    add_undirected("Valencia", "Geneva")
    add_undirected("Valencia", "Munich")

    # Decision variables: city at end of each day (1..25)
    D = [Int(f"D_{d}") for d in range(n_days + 1)]  # we'll ignore D[0]
    s = Solver()

    # Domain constraints
    for d in range(1, n_days + 1):
        s.add(And(D[d] >= 0, D[d] < len(cities)))

    # Presence booleans p[d][c]: True if you are considered in city c on day d
    # According to rule: presence on day d is in D[d], and also in D[d-1] if a flight happens that day.
    # We model presence as: p[d,c] <-> (D[d]==c OR (d>1 AND D[d-1]==c))
    p = [[Bool(f"p_{d}_{c}") for c in range(len(cities))] for d in range(n_days + 1)]
    for d in range(1, n_days + 1):
        for c in range(len(cities)):
            if d == 1:
                s.add(p[d][c] == (D[d] == c))
            else:
                s.add(p[d][c] == Or(D[d] == c, D[d - 1] == c))

    # Flight feasibility: if D[d] != D[d-1], then (D[d-1] -> D[d]) must be a direct flight
    for d in range(2, n_days + 1):
        allowed_transitions = []
        for (a, b) in edges:
            allowed_transitions.append(And(D[d - 1] == a, D[d] == b))
        s.add(Or(D[d] == D[d - 1], Or(allowed_transitions)))

    # Required total presence days per city
    for c_name, req in required_days.items():
        c = idx[c_name]
        s.add(Sum([If(p[d][c], 1, 0) for d in range(1, n_days + 1)]) == req)

    # Day-specific presence requirements
    for d in must_be_reyk_days:
        s.add(p[d][idx["Reykjavik"]] == True)
    for d in must_be_stu_days:
        s.add(p[d][idx["Stuttgart"]] == True)
    for d in must_be_muc_days:
        s.add(p[d][idx["Munich"]] == True)
    for d in must_be_ist_days:
        s.add(p[d][idx["Istanbul"]] == True)

    # Solve
    result = s.check()
    if result == sat:
        m = s.model()
        itinerary = []
        for d in range(1, n_days + 1):
            city_idx = m[D[d]].as_long()
            itinerary.append({"day": d, "place": cities[city_idx]})
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        # If unsat, still output a JSON with an empty itinerary and status
        print(json.dumps({"itinerary": [], "status": str(result)}, indent=2))


if __name__ == "__main__":
    solve_itinerary()
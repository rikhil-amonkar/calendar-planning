import json
from z3 import Solver, Bool, Int, Sum, If, Or, And, sat

def main():
    # Trip parameters
    total_days = 19
    cities = ["Reykjavik", "Istanbul", "Edinburgh", "Oslo", "Stuttgart", "Bucharest"]
    city_index = {c: i for i, c in enumerate(cities)}

    # Required durations per city (in days)
    durations = {
        "Reykjavik": 5,
        "Istanbul": 4,
        "Edinburgh": 5,
        "Oslo": 2,
        "Stuttgart": 3,
        "Bucharest": 5
    }

    # Windows for meeting/visiting
    istanbul_meet_window = (5, 8)  # inclusive
    oslo_visit_window = (8, 9)     # inclusive

    # Direct flight connectivity
    # "A and B" means both directions; "from Reykjavik to Stuttgart" means one direction.
    directed_edges = set()
    def add_undirected(a, b):
        directed_edges.add((a, b))
        directed_edges.add((b, a))
    def add_direct(a, b):
        directed_edges.add((a, b))

    add_undirected("Bucharest", "Oslo")
    add_undirected("Istanbul", "Oslo")
    add_direct("Reykjavik", "Stuttgart")
    add_undirected("Bucharest", "Istanbul")
    add_undirected("Stuttgart", "Edinburgh")
    add_undirected("Istanbul", "Edinburgh")
    add_undirected("Oslo", "Reykjavik")
    add_undirected("Istanbul", "Stuttgart")
    add_undirected("Oslo", "Edinburgh")

    # Number of positions (segments) equals number of cities
    n = len(cities)
    positions = list(range(n))

    # Decision variables: x[i][c] is True iff city c is at position i
    x = [[Bool(f"x_{i}_{city}") for city in cities] for i in positions]

    # Start and end day for each position's stay
    s = [Int(f"s_{i}") for i in positions]
    e = [Int(f"e_{i}") for i in positions]

    solver = Solver()

    # Each position has exactly one city
    for i in positions:
        solver.add(Sum([If(x[i][ci], 1, 0) for ci in range(n)]) == 1)

    # Each city appears exactly once
    for ci in range(n):
        solver.add(Sum([If(x[i][ci], 1, 0) for i in positions]) == 1)

    # Durations per position depend on which city is placed there
    dur_pos = []
    for i in positions:
        dur_i = Sum([If(x[i][ci], durations[cities[ci]], 0) for ci in range(n)])
        dur_pos.append(dur_i)

    # Start and end day constraints
    solver.add(s[0] == 1)
    for i in positions:
        solver.add(e[i] == s[i] + dur_pos[i] - 1)
        solver.add(s[i] >= 1, e[i] >= 1, s[i] <= total_days, e[i] <= total_days)
        solver.add(dur_pos[i] >= 1)  # sanity

    for i in range(1, n):
        # The next city's start day equals the previous city's end day (flight day overlaps)
        solver.add(s[i] == e[i - 1])

    # End on the last day
    solver.add(e[n - 1] == total_days)

    # Direct flight constraints between consecutive positions
    for i in range(n - 1):
        allowed_pairs = []
        for a, b in directed_edges:
            ci = city_index[a]
            di = city_index[b]
            allowed_pairs.append(And(x[i][ci], x[i + 1][di]))
        solver.add(Or(allowed_pairs))

    # City-specific start and end times, derived from position variables
    s_city = {}
    e_city = {}
    for c in cities:
        ci = city_index[c]
        s_c = Int(f"s_city_{c}")
        solver.add(s_c == Sum([If(x[i][ci], s[i], 0) for i in positions]))
        s_city[c] = s_c
        e_city[c] = s_c + durations[c] - 1
        solver.add(s_c >= 1, s_c <= total_days)
        solver.add(e_city[c] >= 1, e_city[c] <= total_days)

    # Window constraints
    # Istanbul overlaps day 5..8
    solver.add(s_city["Istanbul"] <= istanbul_meet_window[1])
    solver.add(e_city["Istanbul"] >= istanbul_meet_window[0])

    # Oslo overlaps day 8..9
    solver.add(s_city["Oslo"] <= oslo_visit_window[1])
    solver.add(e_city["Oslo"] >= oslo_visit_window[0])

    # Durations are already enforced by construction of e_city

    if solver.check() != sat:
        print(json.dumps({"itinerary": [], "status": "UNSAT"}))
        return

    model = solver.model()

    # Extract the ordered itinerary
    itinerary = []
    for i in positions:
        # Identify city at position i
        city_i = None
        for ci, c in enumerate(cities):
            if model.evaluate(x[i][ci], model_completion=True):
                city_i = c
                break
        si = model.evaluate(s[i]).as_long()
        ei = model.evaluate(e[i]).as_long()
        itinerary.append({
            "day_range": f"Day {si}-{ei}",
            "place": city_i
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
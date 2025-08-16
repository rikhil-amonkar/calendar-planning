import json
from z3 import *

def solve_itinerary():
    # Cities and indices
    cities = ["Seville", "Vilnius", "Santorini", "London", "Stuttgart", "Dublin", "Frankfurt"]
    city_to_idx = {c: i for i, c in enumerate(cities)}
    idx_to_city = {i: c for i, c in enumerate(cities)}

    # Direct flight edges (undirected)
    direct_pairs = [
        ("Frankfurt", "Dublin"),
        ("Frankfurt", "London"),
        ("London", "Dublin"),
        ("Vilnius", "Frankfurt"),
        ("Frankfurt", "Stuttgart"),
        ("Dublin", "Seville"),
        ("London", "Santorini"),
        ("Stuttgart", "London"),
        ("Santorini", "Dublin")
    ]
    edges = set()
    for a, b in direct_pairs:
        ia, ib = city_to_idx[a], city_to_idx[b]
        edges.add((ia, ib))
        edges.add((ib, ia))

    # Desired total days per city (counting flight days for both cities)
    target_days = {
        "Seville": 5,
        "Vilnius": 3,
        "Santorini": 2,
        "London": 2,
        "Stuttgart": 3,
        "Dublin": 3,
        "Frankfurt": 5
    }
    targets = [target_days[c] for c in cities]

    N = 17  # total days
    # Variables: c[1..17] as city index each day (1-based indexing for clarity)
    c = [None] + [Int(f"c_{d}") for d in range(1, N + 1)]

    s = Solver()

    # Domain constraints
    for d in range(1, N + 1):
        s.add(And(c[d] >= 0, c[d] < len(cities)))

    # Flight adjacency constraints: if city changes on day d (between day d and d+1), must be direct flight
    changes = []
    for d in range(1, N):
        change = Bool(f"change_{d}")
        changes.append(change)
        # change <-> c[d] != c[d+1]
        s.add(change == (c[d] != c[d + 1]))
        # If change then edge must exist
        allowed = Or([And(c[d] == i, c[d + 1] == j) for (i, j) in edges])
        s.add(Or(c[d] == c[d + 1], allowed))

    # Exactly 6 flight days (because sum of targets is 23, N=17, so overlaps F = 6)
    s.add(Sum([If(ch, 1, 0) for ch in changes]) == 6)

    # Count per city: base days + arrivals must equal targets
    for ci in range(len(cities)):
        base_count = Sum([If(c[d] == ci, 1, 0) for d in range(1, N + 1)])
        arrival_count = Sum([If(And(c[d + 1] == ci, c[d] != c[d + 1]), 1, 0) for d in range(1, N)])
        s.add(base_count + arrival_count == targets[ci])

    # Presence helper: presence(city ci, day t) is true iff
    # - c[t] == ci (you are based in that city that day), OR
    # - (t <= 16 and change on day t and c[t+1] == ci) (arrived into ci on day t)
    def presence(ci, t):
        cond_current = (c[t] == ci)
        cond_arrival = And(t <= N - 1, c[t] != c[t + 1], c[t + 1] == ci)
        return Or(cond_current, cond_arrival)

    # Special constraints:
    # - Be in London on day 9 and day 10 (to meet friends)
    LON = city_to_idx["London"]
    s.add(presence(LON, 9))
    s.add(presence(LON, 10))

    # - Be in Stuttgart on at least one of days 7..9 (to visit relatives)
    STU = city_to_idx["Stuttgart"]
    s.add(Or(presence(STU, 7), presence(STU, 8), presence(STU, 9)))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Build itinerary JSON: list of day-place mappings
    itinerary = []
    for d in range(1, N + 1):
        city_idx = m.evaluate(c[d]).as_long()
        itinerary.append({"day": d, "place": idx_to_city[city_idx]})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False, indent=2))
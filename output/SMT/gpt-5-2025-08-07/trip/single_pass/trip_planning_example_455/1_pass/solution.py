from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ["Reykjavik", "Riga", "Warsaw", "Istanbul", "Krakow"]
    idx = {c: i for i, c in enumerate(cities)}
    n = len(cities)

    # Required total counted days per city (including overlap on flight days)
    req = {
        idx["Reykjavik"]: 7,
        idx["Riga"]: 2,
        idx["Warsaw"]: 3,
        idx["Istanbul"]: 6,
        idx["Krakow"]: 7,
    }

    # Direct flight adjacency (undirected)
    edges = set()
    def add_edge(a, b):
        edges.add((idx[a], idx[b]))
        edges.add((idx[b], idx[a]))

    add_edge("Istanbul", "Krakow")
    add_edge("Warsaw", "Reykjavik")
    add_edge("Istanbul", "Warsaw")
    add_edge("Riga", "Istanbul")
    add_edge("Krakow", "Warsaw")
    add_edge("Riga", "Warsaw")

    total_days = 21
    flights_needed = 4  # Because total required counted days = 25; 21 + flights = 25 -> flights=4

    s = Solver()

    # isPos[k][c] = city c is at itinerary segment position k (k=0..4)
    isPos = [[Bool(f"isPos_{k}_{c}") for c in range(n)] for k in range(n)]

    # Each position has exactly one city
    for k in range(n):
        s.add(Sum([If(isPos[k][c], 1, 0) for c in range(n)]) == 1)
    # Each city appears exactly once
    for c in range(n):
        s.add(Sum([If(isPos[k][c], 1, 0) for k in range(n)]) == 1)

    # Segment lengths L[k] (number of labeled days for position k city)
    L = [Int(f"L_{k}") for k in range(n)]
    for k in range(n):
        # If position k is the last segment (k=4), L = req[city]
        # Otherwise L = req[city] - 1 (since the city also counts its departure day, which is next segment's first day)
        offs = 0 if k == n - 1 else 1
        s.add(L[k] == Sum([If(isPos[k][c], req[c] - offs, 0) for c in range(n)]))
        s.add(L[k] >= 1)

    # Prefix sums P[k] = sum_{i<k} L[i], with P[0]=0 and P[5]=21 (total days)
    P = [Int(f"P_{k}") for k in range(n + 1)]
    s.add(P[0] == 0)
    for k in range(n):
        s.add(P[k + 1] == P[k] + L[k])
    s.add(P[n] == total_days)

    # Adjacency constraints between consecutive segments (direct flight)
    for k in range(1, n):
        for a in range(n):
            for b in range(n):
                s.add(Implies(And(isPos[k - 1][a], isPos[k][b]), (a, b) in edges))

    # Helper: InCity(c, d) -> BoolExpr that is true if on day d we are "in" city c
    # Being "in" city c on day d is defined as:
    # - d within [1+P[k], P[k]+L[k]] if city c is at position k (its labeled days)
    # - OR (if k<4) d == 1 + P[k] + L[k] (the departure day counts for city c as well)
    def InCity(c, d):
        labeled = []
        depart = []
        for k in range(n):
            labeled.append(And(isPos[k][c], d >= 1 + P[k], d <= P[k] + L[k]))
            if k < n - 1:
                depart.append(And(isPos[k][c], d == 1 + P[k] + L[k]))
        return Or(*(labeled + depart))

    # Exact counted days per city must match requirements
    for c in range(n):
        s.add(Sum([If(InCity(c, d), 1, 0) for d in range(1, total_days + 1)]) == req[c])

    # Special constraints:
    # - Meet a friend in Riga on day 1 or day 2 (be in Riga on day 1 or 2)
    s.add(Or(InCity(idx["Riga"], 1), InCity(idx["Riga"], 2)))

    # - Attend a wedding in Istanbul on some day between day 2 and day 7 (inclusive)
    s.add(Or([InCity(idx["Istanbul"], d) for d in range(2, 8)]))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No solution found by Z3.")

    m = s.model()

    # Extract the permutation and lengths
    perm = [None] * n
    lengths = [int(m[L[k]].as_long()) for k in range(n)]
    for k in range(n):
        for c in range(n):
            if is_true(m[isPos[k][c]]):
                perm[k] = c
                break

    # Build the day-by-day itinerary (label: city at end of day d)
    itinerary = []
    day = 1
    for k in range(n):
        city_name = cities[perm[k]]
        for _ in range(lengths[k]):
            itinerary.append({"day": day, "city": city_name})
            day += 1

    # Output JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_itinerary()
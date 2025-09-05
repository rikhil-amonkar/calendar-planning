import json
from z3 import *

def solve_itinerary():
    # Parameters
    days_total = 17
    cities = ["Warsaw", "Budapest", "Paris", "Riga"]
    W, B, P, R = 0, 1, 2, 3  # City codes

    # Desired city-day totals (counting travel day for both cities)
    target_days = {
        W: 2,  # Warsaw
        B: 7,  # Budapest
        P: 4,  # Paris
        R: 7,  # Riga
    }

    # Direct flight connections (undirected edges)
    direct_edges = {(W, B), (W, R), (B, P), (W, P), (P, R)}

    # Z3 Solver
    s = Solver()

    # City assignment per day (1-based days), city[d-1] in {W, B, P, R}
    city = [Int(f"city_{d}") for d in range(1, days_total + 1)]
    for d in range(days_total):
        s.add(And(city[d] >= 0, city[d] <= 3))

    # Transition indicators for days 2..17 (1 if flight on that day)
    trans = [Int(f"trans_{d}") for d in range(2, days_total + 1)]
    for idx, d in enumerate(range(2, days_total + 1)):
        s.add(Or(trans[idx] == 0, trans[idx] == 1))
        s.add(trans[idx] == If(city[d - 2] != city[d - 1], 1, 0))  # day d transition means city[d-2] -> city[d-1]

        # Enforce direct flights if a transition happens
        allowed = Or(*[
            And(city[d - 2] == a, city[d - 1] == b) for (a, b) in direct_edges
        ] + [
            And(city[d - 2] == b, city[d - 1] == a) for (a, b) in direct_edges
        ])
        s.add(Implies(city[d - 2] != city[d - 1], allowed))

    # Exactly 3 flights (so 4 city segments)
    s.add(Sum(trans) == 3)

    # Helper: presence in a city on a given day (counts travel day for both)
    def in_city_on_day(c, d):
        # d is 1-based
        if d == 1:
            return city[0] == c
        else:
            return Or(
                city[d - 1] == c,                   # assigned to c on day d
                And(city[d - 2] == c, city[d - 2] != city[d - 1])  # flew out of c on day d
            )

    # Attend Warsaw show on Day 1-2 (present in Warsaw on both days)
    s.add(in_city_on_day(W, 1))
    s.add(in_city_on_day(W, 2))

    # Attend wedding in Riga on some day in Day 11-17 (present in Riga at least one of these days)
    s.add(Or([in_city_on_day(R, d) for d in range(11, 18)]))

    # City-day totals with travel-day double counting
    for c in [W, B, P, R]:
        count_c = Sum(
            # Base presence (assigned city each day)
            *[If(city[d - 1] == c, 1, 0) for d in range(1, days_total + 1)],
            # Extra counts on transition days for the previous city
            *[If(And(city[d - 2] == c, city[d - 2] != city[d - 1]), 1, 0) for d in range(2, days_total + 1)]
        )
        s.add(count_c == target_days[c])

    # Must visit each city at least once (redundant with above counts, but explicit)
    for c in [W, B, P, R]:
        s.add(Or([city[d] == c for d in range(days_total)]))

    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    m = s.model()

    # Extract itinerary segments as contiguous ranges of the assigned city per day
    city_vals = [m.evaluate(city[d]).as_long() for d in range(days_total)]

    itinerary = []
    start = 1
    curr = city_vals[0]
    for d in range(2, days_total + 1):
        if city_vals[d - 1] != curr:
            itinerary.append({
                "day_range": f"Day {start}-{d - 1}",
                "place": cities[curr]
            })
            start = d
            curr = city_vals[d - 1]
    # Append final segment
    itinerary.append({
        "day_range": f"Day {start}-{days_total}",
        "place": cities[curr]
    })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result))
# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json

def solve_itinerary():
    # Cities (index map)
    cities = ["Oslo", "Stuttgart", "Reykjavik", "Split", "Geneva", "Porto", "Tallinn", "Stockholm"]
    idx = {c: i for i, c in enumerate(cities)}

    # Trip length
    D = 21
    days = list(range(1, D + 1))

    # Required (total) days per city (counting flight days for both origin and destination as per spec)
    required = {
        "Oslo": 5,
        "Stuttgart": 5,
        "Reykjavik": 2,
        "Split": 3,
        "Geneva": 2,
        "Porto": 3,
        "Tallinn": 5,
        "Stockholm": 3,
    }

    # Direct flights (undirected)
    flight_pairs = [
        ("Reykjavik", "Stuttgart"),
        ("Reykjavik", "Stockholm"),
        ("Reykjavik", "Tallinn"),
        ("Stockholm", "Oslo"),
        ("Stuttgart", "Porto"),
        ("Oslo", "Split"),
        ("Stockholm", "Stuttgart"),
        ("Reykjavik", "Oslo"),
        ("Oslo", "Geneva"),
        ("Stockholm", "Split"),
        ("Split", "Stuttgart"),
        ("Tallinn", "Oslo"),
        ("Stockholm", "Geneva"),
        ("Oslo", "Porto"),
        ("Geneva", "Porto"),
        ("Geneva", "Split"),
    ]
    # Build adjacency matrix
    n = len(cities)
    adj = [[False] * n for _ in range(n)]
    for a, b in flight_pairs:
        ia, ib = idx[a], idx[b]
        adj[ia][ib] = True
        adj[ib][ia] = True

    # Z3 variables: city per day
    city = [Int(f"city_{d}") for d in days]

    s = Optimize()  # Use Optimize to allow future soft constraints or just as a solver
    for v in city:
        s.add(Or([v == i for i in range(n)]))

    # Change indicator between consecutive days
    change = [Bool(f"change_{d}") for d in days]
    s.add(change[0] == False)  # Day 1 has no "change"
    for d in range(2, D + 1):
        s.add(change[d - 1] == (city[d - 1 - 1] != city[d - 1]))

    # Direct flight constraint when changing cities
    for d in range(2, D + 1):
        prev = city[d - 2]
        cur = city[d - 1]
        # If no change, OK; if change, must be direct flight
        s.add(Implies(prev != cur, Or([And(prev == i, cur == j) for i in range(n) for j in range(n) if adj[i][j]])))

    # "Presence" in a city on a given day (counts double on flight days per spec)
    # presence[c][d] is True iff:
    #   - city[d] == c (assigned there), OR
    #   - (d >= 2 and city[d-1] == c and city[d] != city[d-1]) i.e., departure day counts for origin as well
    presence = [[Bool(f"presence_{c}_{d}") for d in days] for c in cities]
    for ci, cname in enumerate(cities):
        for d in days:
            if d == 1:
                s.add(presence[ci][d - 1] == (city[d - 1] == ci))
            else:
                s.add(presence[ci][d - 1] == Or(
                    city[d - 1] == ci,
                    And(city[d - 2] == ci, city[d - 1] != city[d - 2])
                ))

    # Total days per city must match requirement
    for cname, req in required.items():
        ci = idx[cname]
        s.add(Sum([If(presence[ci][d - 1], 1, 0) for d in days]) == req)

    # Transitions count equals sum_of_required_days - D (because flight days are double-counted)
    sum_required = sum(required.values())
    s.add(Sum([If(change[d - 1], 1, 0) for d in days]) == sum_required - D)

    # Conference in Reykjavik on day 1 and day 2 (must be present in Reykjavik those days)
    s.add(presence[idx["Reykjavik"]][0] == True)  # Day 1
    s.add(presence[idx["Reykjavik"]][1] == True)  # Day 2

    # Workshop in Porto between day 19 and day 21 (must be present on each of those days)
    for d in [19, 20, 21]:
        s.add(presence[idx["Porto"]][d - 1] == True)

    # Meet a friend in Stockholm between day 2 and day 4 (present at least one of these days)
    s.add(Or([presence[idx["Stockholm"]][d - 1] for d in [2, 3, 4]]))

    # Solve
    if s.check() != sat:
        # No solution under the given constraints
        print(json.dumps({"itinerary": [], "status": "unsat"}))
        return

    m = s.model()
    itinerary = []
    for d in days:
        city_id = m[city[d - 1]].as_long()
        itinerary.append({"day": d, "city": cities[city_id]})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    solve_itinerary()
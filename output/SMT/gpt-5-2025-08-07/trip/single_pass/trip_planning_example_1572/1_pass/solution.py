import json
from z3 import *

def solve_itinerary():
    # Cities and indices
    cities = ["Lyon","Paris","Riga","Berlin","Stockholm","Zurich","Nice","Seville","Milan","Naples"]
    idx = {c:i for i,c in enumerate(cities)}
    n_days = 23
    d_range = range(n_days)  # 0..22 represent Day 1..23

    # Required total day counts per city
    required = {
        "Lyon": 3,
        "Paris": 5,
        "Riga": 2,
        "Berlin": 2,
        "Stockholm": 3,
        "Zurich": 5,
        "Nice": 2,
        "Seville": 3,
        "Milan": 3,
        "Naples": 4,
    }

    # Direct flights (undirected)
    direct_pairs = [
        ("Paris","Stockholm"),
        ("Seville","Paris"),
        ("Naples","Zurich"),
        ("Nice","Riga"),
        ("Berlin","Milan"),
        ("Paris","Zurich"),
        ("Paris","Nice"),
        ("Milan","Paris"),
        ("Milan","Riga"),
        ("Paris","Lyon"),
        ("Milan","Naples"),
        ("Paris","Riga"),
        ("Berlin","Stockholm"),
        ("Stockholm","Riga"),
        ("Nice","Zurich"),
        ("Milan","Zurich"),
        ("Lyon","Nice"),
        ("Zurich","Stockholm"),
        ("Zurich","Riga"),
        ("Berlin","Naples"),
        ("Milan","Stockholm"),
        ("Berlin","Zurich"),
        ("Milan","Seville"),
        ("Paris","Naples"),
        ("Berlin","Riga"),
        ("Nice","Stockholm"),
        ("Berlin","Paris"),
        ("Nice","Naples"),
        ("Berlin","Nice"),
    ]

    # Build adjacency set with both directions
    adj = set()
    for a,b in direct_pairs:
        adj.add((idx[a], idx[b]))
        adj.add((idx[b], idx[a]))

    # Z3 variables: city per day (0..9)
    city = [Int(f"city_day_{d+1}") for d in d_range]

    s = Solver()

    # Domain constraints
    for d in d_range:
        s.add(And(city[d] >= 0, city[d] < len(cities)))

    # Movement constraints: if city changes from day d-1 to day d, it must be a direct flight.
    # Staying (same city) is always allowed.
    for d in range(1, n_days):
        same = city[d] == city[d-1]
        # Or one of the allowed pairs
        allowed_moves = [And(city[d-1] == a, city[d] == b) for (a,b) in adj]
        s.add(Or(same, Or(*allowed_moves)))

    # Helper: indicator as Int 0/1
    def I(b):
        return If(b, 1, 0)

    # Count per city with flight-day double counting rule:
    # count(c) = sum_d [city[d]==c] + sum_{d>=1} [city[d-1]==c and city[d]!=city[d-1]]
    for cname, need in required.items():
        c = idx[cname]
        assigned = Sum([I(city[d] == c) for d in d_range])
        depart_counted = Sum([I(And(city[d-1] == c, city[d] != city[d-1])) for d in range(1, n_days)])
        s.add(assigned + depart_counted == need)

    # Helper: presence on a given day t in city c (day index 0-based)
    # present(t,c) = (city[t]==c) or (t>=1 and city[t-1]==c and city[t]!=city[t-1])
    def present(day_idx, c):
        if day_idx == 0:
            return city[0] == c
        return Or(city[day_idx] == c, And(city[day_idx-1] == c, city[day_idx] != city[day_idx-1]))

    # Event constraints:
    # Berlin wedding Day 1-2 -> present on days 0 and 1 in Berlin
    s.add(present(0, idx["Berlin"]))
    s.add(present(1, idx["Berlin"]))

    # Nice workshop Day 12-13 -> present on days 11 and 12 in Nice
    s.add(present(11, idx["Nice"]))
    s.add(present(12, idx["Nice"]))

    # Stockholm show Day 20-22 -> present on days 19,20,21 in Stockholm
    s.add(present(19, idx["Stockholm"]))
    s.add(present(20, idx["Stockholm"]))
    s.add(present(21, idx["Stockholm"]))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()
    itinerary = []
    for d in d_range:
        c_id = m.evaluate(city[d]).as_long()
        itinerary.append({"day": d+1, "city": cities[c_id]})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    plan = solve_itinerary()
    print(json.dumps(plan, indent=2))
from z3 import *
import json

def solve_itinerary():
    # Cities and indexing
    cities = ["Oslo", "Reykjavik", "Stockholm", "Munich", "Frankfurt", "Barcelona", "Bucharest", "Split"]
    idx = {c: i for i, c in enumerate(cities)}

    # Undirected direct flights (edges)
    edges = [
        ("Reykjavik","Munich"),
        ("Munich","Frankfurt"),
        ("Split","Oslo"),
        ("Reykjavik","Oslo"),
        ("Bucharest","Munich"),
        ("Oslo","Frankfurt"),
        ("Bucharest","Barcelona"),
        ("Barcelona","Frankfurt"),
        ("Reykjavik","Frankfurt"),
        ("Barcelona","Stockholm"),
        ("Barcelona","Reykjavik"),
        ("Stockholm","Reykjavik"),
        ("Barcelona","Split"),
        ("Bucharest","Oslo"),
        ("Bucharest","Frankfurt"),
        ("Split","Stockholm"),
        ("Barcelona","Oslo"),
        ("Stockholm","Munich"),
        ("Stockholm","Oslo"),
        ("Split","Frankfurt"),
        ("Barcelona","Munich"),
        ("Stockholm","Frankfurt"),
        ("Munich","Oslo"),
        ("Split","Munich"),
    ]
    # Build set of undirected adjacency
    adj = set()
    for a, b in edges:
        adj.add(frozenset({idx[a], idx[b]}))

    # Duration requirements
    must_days = {
        "Oslo": 2,
        "Reykjavik": 5,
        "Stockholm": 4,
        "Munich": 4,
        "Frankfurt": 4,
        "Barcelona": 3,
        "Bucharest": 2,
        "Split": 3,
    }
    req = {idx[k]: v for k, v in must_days.items()}

    days = 20
    x = [Int(f"x_{d+1}") for d in range(days)]
    s = Solver()

    # Domain constraints
    for d in range(days):
        s.add(And(x[d] >= 0, x[d] < len(cities)))

    # Direct flight constraints: if city changes between consecutive days, it must be an allowed edge
    for d in range(1, days):
        # Forbid every disallowed change pair (a -> b) where a != b and no edge exists
        for a in range(len(cities)):
            for b in range(len(cities)):
                if a != b and frozenset({a, b}) not in adj:
                    s.add(Not(And(x[d-1] == a, x[d] == b)))
        # Staying in the same city is allowed implicitly

    # Helper: inCity(c, d_day) according to the "flight day counts for both cities" rule
    def in_city(c, d_day):
        # d_day is 1-based
        i = d_day - 1
        same = (x[i] == c)
        if d_day == 1:
            return same
        prev = (x[i-1] == c)
        changed = (x[i] != x[i-1])
        # If there is a flight on day d_day and previous day was c, then day d_day counts for c too
        return Or(same, And(prev, changed))

    # Duration constraints per city
    for c in range(len(cities)):
        s.add(Sum([If(in_city(c, d+1), 1, 0) for d in range(days)]) == req[c])

    # Windows:
    # Oslo show on days 16 and 17 (must be "in" Oslo both days)
    s.add(in_city(idx["Oslo"], 16))
    s.add(in_city(idx["Oslo"], 17))

    # Reykjavik: meet friend between day 9 and 13 (inclusive)
    s.add(Or([in_city(idx["Reykjavik"], d) for d in range(9, 14)]))

    # Munich: visit relatives between day 13 and 16 (inclusive)
    s.add(Or([in_city(idx["Munich"], d) for d in range(13, 17)]))

    # Frankfurt workshop between day 17 and 20 (inclusive)
    s.add(Or([in_city(idx["Frankfurt"], d) for d in range(17, 21)]))

    # Optional: enforce the implied number of flight days = sum(durations) - total days = 27 - 20 = 7
    flight_days = Sum([If(x[d] != x[d-1], 1, 0) for d in range(1, days)])
    s.add(flight_days == 7)

    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found.")
    m = s.model()

    itinerary = []
    for d in range(1, days+1):
        city_id = m[x[d-1]].as_long()
        itinerary.append({"day": d, "place": cities[city_id]})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_itinerary()
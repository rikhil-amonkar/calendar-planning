# Solve the trip planning problem using Z3 and output a JSON itinerary.
from z3 import *
import json

def solve_itinerary():
    # Cities and mapping
    cities = ["Prague", "Lyon", "Frankfurt", "Helsinki", "Naples"]
    C = {name: idx for idx, name in enumerate(cities)}
    n_days = 12

    # Direct flights (undirected)
    edges = {
        ("Prague", "Lyon"),
        ("Prague", "Frankfurt"),
        ("Frankfurt", "Lyon"),
        ("Helsinki", "Naples"),
        ("Helsinki", "Frankfurt"),
        ("Naples", "Frankfurt"),
        ("Prague", "Helsinki"),
    }
    allowed_pairs = set()
    for a, b in edges:
        allowed_pairs.add((C[a], C[b]))
        allowed_pairs.add((C[b], C[a]))

    # Required total "presence" days per city (counting flight days for both)
    required_days = {
        C["Frankfurt"]: 3,
        C["Naples"]: 4,
        C["Helsinki"]: 4,
        C["Lyon"]: 3,
        C["Prague"]: 2,
    }

    # Z3 variables
    Day = [Int(f"Day_{d}") for d in range(1, n_days + 1)]
    present = {
        (c, d): Bool(f"present_{cities[c]}_day{d}")
        for c in range(len(cities))
        for d in range(1, n_days + 1)
    }

    s = Solver()

    # Domain constraints for each day
    for d in range(n_days):
        s.add(Or([Day[d] == c for c in range(len(cities))]))

    # Presence constraints
    # Day 1: only the assigned city is present
    for c in range(len(cities)):
        s.add(present[(c, 1)] == (Day[0] == c))

    # Days 2..n: if we switch, both previous and current cities are present; else only the (same) city is present
    for d in range(2, n_days + 1):
        prev = Day[d - 2]
        cur = Day[d - 1]
        for c in range(len(cities)):
            s.add(present[(c, d)] == Or(cur == c, And(prev == c, cur != prev)))

    # Direct flight constraints: if there is a switch between consecutive days, it must be an allowed edge
    for d in range(2, n_days + 1):
        prev = Day[d - 2]
        cur = Day[d - 1]
        switch = cur != prev
        allowed_disj = Or([And(prev == a, cur == b) for (a, b) in allowed_pairs])
        s.add(Implies(switch, allowed_disj))

    # City presence totals
    for c, req in required_days.items():
        s.add(Sum([If(present[(c, d)], 1, 0) for d in range(1, n_days + 1)]) == req)

    # Helsinki show from Day 2 to Day 5 (must be present in Helsinki on days 2..5)
    for d in range(2, 6):
        s.add(present[(C["Helsinki"], d)] == True)

    # Prague workshop on Day 1 or Day 2 (presence suffices, including flight overlap)
    s.add(Or(present[(C["Prague"], 1)], present[(C["Prague"], 2)]))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found.")

    m = s.model()

    itinerary = []
    for d in range(1, n_days + 1):
        city_idx = m[Day[d - 1]].as_long()
        itinerary.append({"day": d, "city": cities[city_idx]})

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    solve_itinerary()
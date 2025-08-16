# Requires: z3-solver
# This program finds a 23-day itinerary across 10 cities using only direct flights
# and respecting city-day requirements with the "flight day counts for both cities" rule.
# Interpretation notes:
# - If day d city != day d-1 city, then a flight happens on day d and that day counts
#   for BOTH the previous day's city and the current day's city.
# - "Meet friends at Mykonos between day 10 and day 11" is modeled as being in Mykonos
#   on at least one of those two days (day 10 or day 11). This interpretation is necessary
#   to keep the exact 2-day total in Mykonos under the given counting rules.

from z3 import *
import json

def main():
    # Cities
    cities = [
        "Rome", "Mykonos", "Lisbon", "Frankfurt", "Nice",
        "Stuttgart", "Venice", "Dublin", "Bucharest", "Seville"
    ]
    idx = {c: i for i, c in enumerate(cities)}

    # Direct flights (undirected)
    direct_pairs = [
        ("Rome", "Stuttgart"),
        ("Venice", "Rome"),
        ("Dublin", "Bucharest"),
        ("Mykonos", "Rome"),
        ("Seville", "Lisbon"),
        ("Frankfurt", "Venice"),
        ("Venice", "Stuttgart"),
        ("Bucharest", "Lisbon"),
        ("Nice", "Mykonos"),
        ("Venice", "Lisbon"),
        ("Dublin", "Lisbon"),
        ("Venice", "Dublin"),
        ("Venice", "Nice"),
        ("Rome", "Seville"),
        ("Frankfurt", "Rome"),
        ("Nice", "Dublin"),
        ("Rome", "Bucharest"),
        ("Frankfurt", "Dublin"),
        ("Rome", "Dublin"),
        ("Venice", "Dublin"),  # duplicate, harmless
        ("Rome", "Lisbon"),
        ("Frankfurt", "Lisbon"),
        ("Nice", "Rome"),
        ("Frankfurt", "Nice"),
        ("Frankfurt", "Stuttgart"),
        ("Frankfurt", "Bucharest"),
        ("Lisbon", "Stuttgart"),
        ("Nice", "Lisbon"),
        ("Seville", "Dublin"),
    ]
    allowed = set()
    for a, b in direct_pairs:
        allowed.add((idx[a], idx[b]))
        allowed.add((idx[b], idx[a]))

    # Required total "days" per city under the counting convention
    required = {
        "Rome": 3,
        "Mykonos": 2,
        "Lisbon": 2,
        "Frankfurt": 5,
        "Nice": 3,
        "Stuttgart": 4,
        "Venice": 4,
        "Dublin": 2,
        "Bucharest": 2,
        "Seville": 5,
    }
    req = {idx[k]: v for k, v in required.items()}

    n_days = 23
    n_cities = len(cities)

    # Variables: day_city[d] = city index for day d (1..23) -> use 0..22 in Python
    day_city = [Int(f"day_{d+1}") for d in range(n_days)]

    s = Solver()

    # Domain constraints
    for d in range(n_days):
        s.add(And(day_city[d] >= 0, day_city[d] < n_cities))

    # Conference in Seville on day 13 and day 17
    s.add(day_city[12] == idx["Seville"])  # day 13
    s.add(day_city[16] == idx["Seville"])  # day 17

    # Wedding in Frankfurt between day 1 and day 5 (at least one of these days)
    s.add(Or([day_city[d] == idx["Frankfurt"] for d in range(0, 5)]))

    # Meet friends in Mykonos between day 10 and day 11 (at least one of these two days)
    s.add(Or(day_city[9] == idx["Mykonos"], day_city[10] == idx["Mykonos"]))

    # Flight feasibility: consecutive different cities must be directly connected
    # For each day transition (d-1) -> d, forbid non-edges when cities differ.
    non_edges = []
    for u in range(n_cities):
        for v in range(n_cities):
            if u == v:
                continue
            if (u, v) not in allowed:
                non_edges.append((u, v))
    for d in range(1, n_days):
        for (u, v) in non_edges:
            # Not( day[d-1]==u and day[d]==v )
            s.add(Not(And(day_city[d-1] == u, day_city[d] == v)))

    # Counting rule:
    # - Base count for city c: number of days where day_city[d] == c
    # - Extra count (departures): number of d>=2 where day_city[d] != day_city[d-1] and day_city[d-1] == c
    # Total for city c = base + extra must equal required[c]
    for c in range(n_cities):
        base = Sum([If(day_city[d] == c, 1, 0) for d in range(n_days)])
        extra = Sum([If(And(day_city[d] != day_city[d-1], day_city[d-1] == c), 1, 0) for d in range(1, n_days)])
        s.add(base + extra == req[c])

    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    m = s.model()
    itinerary = []
    for d in range(n_days):
        city_idx = m[day_city[d]].as_long()
        itinerary.append({"day": d+1, "city": cities[city_idx]})

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()
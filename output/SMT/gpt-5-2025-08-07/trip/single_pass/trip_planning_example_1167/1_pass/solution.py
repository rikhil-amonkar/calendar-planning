# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json

def main():
    # Cities and durations (target counted days per city)
    cities = [
        "Dublin",
        "Brussels",
        "Mykonos",
        "Frankfurt",
        "Krakow",
        "Istanbul",
        "Venice",
        "Naples",
    ]
    idx = {c: i for i, c in enumerate(cities)}
    durations = {
        "Dublin": 5,
        "Krakow": 4,
        "Istanbul": 3,
        "Venice": 3,
        "Naples": 4,
        "Brussels": 2,
        "Mykonos": 4,
        "Frankfurt": 3,
    }

    # Direct flights
    edges = set()
    def add_und(a, b):
        edges.add((idx[a], idx[b]))
        edges.add((idx[b], idx[a]))
    def add_dir(a, b):
        edges.add((idx[a], idx[b]))

    # Given direct flights in the prompt
    add_und("Dublin", "Brussels")
    add_und("Mykonos", "Naples")
    add_und("Venice", "Istanbul")
    add_und("Frankfurt", "Krakow")
    add_und("Naples", "Dublin")
    add_und("Krakow", "Brussels")
    add_und("Naples", "Istanbul")
    add_und("Naples", "Brussels")
    add_und("Istanbul", "Frankfurt")
    add_dir("Brussels", "Frankfurt")   # directed
    add_und("Istanbul", "Krakow")
    add_und("Istanbul", "Brussels")
    add_und("Venice", "Frankfurt")
    add_und("Naples", "Frankfurt")
    add_und("Dublin", "Krakow")
    add_und("Venice", "Brussels")
    add_und("Naples", "Venice")
    add_und("Istanbul", "Dublin")
    add_und("Venice", "Dublin")
    add_und("Dublin", "Frankfurt")

    # Time horizon
    T = 21
    city = [Int(f"city_{d}") for d in range(1, T + 1)]

    s = Solver()

    # Domain constraints
    for d in range(T):
        s.add(And(city[d] >= 0, city[d] < len(cities)))

    # Helper: "in-city on day t" per problem's flight-day rule:
    # You are in city C on day t if:
    # - city[t] == C (assigned), OR
    # - t <= T-1 and city[t+1] == C (you flew into C on day t, counting for both cities)
    def in_city_day(t_idx0, c_idx):
        # t_idx0 is 0-based day index
        same_day = city[t_idx0] == c_idx
        inbound = And(t_idx0 <= T - 2, city[t_idx0 + 1] == c_idx)
        return Or(same_day, inbound)

    # Flight constraints: if city changes between day d and d+1, then it must be a direct flight
    def direct(u, v):
        return Or([And(u == a, v == b) for (a, b) in edges]) if edges else False

    for d in range(T - 1):
        s.add(Implies(city[d] != city[d + 1], direct(city[d], city[d + 1])))

    # Duration constraints: counted days per city
    for cname, k in durations.items():
        c_idx = idx[cname]
        counted = []
        # Assigned-day counts
        for d in range(T):
            counted.append(If(city[d] == c_idx, IntVal(1), IntVal(0)))
        # Inbound flight days count for arrival city (day d counts if city[d+1] == c and city[d] != c)
        for d in range(T - 1):
            counted.append(If(And(city[d] != c_idx, city[d + 1] == c_idx), IntVal(1), IntVal(0)))
        s.add(Sum(counted) == k)

    # Time-window constraints:
    # Dublin: must be in Dublin on days 11-15 inclusive
    for t in range(11, 16):
        s.add(in_city_day(t - 1, idx["Dublin"]))

    # Istanbul: meet friend between day 9 and 11 (at least one day in that window)
    s.add(Or([in_city_day(t - 1, idx["Istanbul"]) for t in range(9, 12)]))

    # Mykonos: visit relatives between day 1 and 4 (at least one day in that window)
    s.add(Or([in_city_day(t - 1, idx["Mykonos"]) for t in range(1, 5)]))

    # Frankfurt: meet friends between day 15 and 17 (at least one day in that window)
    s.add(Or([in_city_day(t - 1, idx["Frankfurt"]) for t in range(15, 18)]))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found.")
    m = s.model()

    # Build output JSON
    itinerary = []
    for d in range(T):
        cval = m[city[d]].as_long()
        itinerary.append({"day": d + 1, "place": cities[cval]})

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()
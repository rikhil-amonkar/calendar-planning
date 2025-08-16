# Requires: z3-solver
# This program finds a valid 18-day itinerary across 8 cities using Z3
# and prints a JSON dictionary with an 'itinerary' list of day-place mappings.

from z3 import *
import json

def solve_itinerary():
    # Cities and indices
    cities = ["Oslo", "Krakow", "Vilnius", "Helsinki", "Dubrovnik", "Madrid", "Paris", "Mykonos"]
    idx = {name: i for i, name in enumerate(cities)}
    N = len(cities)
    DAYS = 18

    # Required total counted days in each city
    req = {
        "Mykonos": 4,
        "Krakow": 5,
        "Vilnius": 2,
        "Helsinki": 2,
        "Dubrovnik": 3,
        "Oslo": 2,
        "Madrid": 5,
        "Paris": 2,
    }

    # Build allowed direct flight pairs (include stay (u,u))
    allowed_pairs = set()
    for u in range(N):
        allowed_pairs.add((u, u))  # staying is always allowed

    def add_sym(a, b):
        allowed_pairs.add((idx[a], idx[b]))
        allowed_pairs.add((idx[b], idx[a]))

    def add_dir(a, b):
        allowed_pairs.add((idx[a], idx[b]))

    # Add given direct flights
    add_sym("Oslo", "Krakow")
    add_sym("Oslo", "Paris")
    add_sym("Paris", "Madrid")
    add_sym("Helsinki", "Vilnius")
    add_sym("Oslo", "Madrid")
    add_sym("Oslo", "Helsinki")
    add_sym("Helsinki", "Krakow")
    add_sym("Dubrovnik", "Helsinki")
    add_sym("Dubrovnik", "Madrid")
    add_sym("Oslo", "Dubrovnik")
    add_sym("Krakow", "Paris")
    add_sym("Madrid", "Mykonos")
    add_sym("Oslo", "Vilnius")
    add_dir("Krakow", "Vilnius")  # directed
    add_sym("Helsinki", "Paris")
    add_sym("Vilnius", "Paris")
    add_sym("Helsinki", "Madrid")

    # Decision variables: city on each day (1..18). We'll use 0-based indexing for Python lists: day 0..17
    c = [Int(f"c_{d+1}") for d in range(DAYS)]

    s = Optimize()  # Optimize/solver (Optimize used just in case; plain Solver would also work)

    # Domain constraints
    for d in range(DAYS):
        s.add(And(c[d] >= 0, c[d] < N))

    # Adjacency constraints for every transition day d>=2 (i.e., day index 1..17)
    # If c[d] != c[d-1], then (c[d-1], c[d]) must be in allowed_pairs; this is encoded by enumerating allowed pairs
    for d in range(1, DAYS):
        s.add(Or([And(c[d-1] == u, c[d] == v) for (u, v) in allowed_pairs]))

    # Helper: "counted" presence for city i on day d (1-based in description, 0-based in code)
    # counted(day d, city i) is True if c[d]==i, or if day d is a flight day and c[d-1]==i
    def counted(d, i):
        if d == 0:
            return c[d] == i
        return Or(c[d] == i, And(c[d] != c[d-1], c[d-1] == i))

    # Total city-day counts must match requirements
    for name, need in req.items():
        i = idx[name]
        s.add(Sum([If(counted(d, i), 1, 0) for d in range(DAYS)]) == need)

    # Oslo friends: be in Oslo on day 1 and day 2 (counted presence), and exactly 2 days total in Oslo
    s.add(c[0] == idx["Oslo"])              # Day 1 must be Oslo (forces counted day1)
    s.add(If(counted(1, idx["Oslo"]), 1, 0) == 1)  # Day 2 counted in Oslo
    # Ensure Oslo only appears as Day 1 city and contributes via flight on Day 2; no more Oslo later
    for d in range(1, DAYS):
        s.add(c[d] != idx["Oslo"])

    # Dubrovnik show: be in Dubrovnik on days 2-4 (counted), total exactly 3 days in Dubrovnik
    # We fix: Day 2 and Day 3 are mapped to Dubrovnik, and we depart Dubrovnik on Day 4,
    # so counted days for Dubrovnik are exactly 2,3,4.
    s.add(c[1] == idx["Dubrovnik"])  # Day 2
    s.add(c[2] == idx["Dubrovnik"])  # Day 3
    # Depart on Day 4 (so Day 4 is counted for Dubrovnik via departure, but not mapped to Dubrovnik)
    s.add(c[3] != idx["Dubrovnik"])
    # No Dubrovnik anywhere else
    for d in list(range(0, 1)) + list(range(3, DAYS)):
        if d not in (1, 2):  # already set 1,2 as Dubrovnik
            s.add(c[d] != idx["Dubrovnik"])

    # Mykonos family visit: exactly days 15-18 (counted). We enforce mapping Mykonos on days 15-18 and nowhere else.
    for d in range(14, 18):  # Days 15..18
        s.add(c[d] == idx["Mykonos"])
    for d in range(0, 14):   # Days 1..14
        s.add(c[d] != idx["Mykonos"])

    # Enforce exact total number of flights = sum(required) - total days
    total_required = sum(req.values())
    s.add(Sum([If(c[d] != c[d-1], 1, 0) for d in range(1, DAYS)]) == (total_required - DAYS))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()
    itinerary = []
    for d in range(DAYS):
        city_name = cities[m[c[d]].as_long()]
        itinerary.append({"day": d + 1, "city": city_name})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_itinerary()
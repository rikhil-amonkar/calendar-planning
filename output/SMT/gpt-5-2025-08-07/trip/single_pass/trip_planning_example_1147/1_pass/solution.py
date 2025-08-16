# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json

def solve_itinerary():
    # Define cities
    cities = ["Brussels", "Helsinki", "Split", "Dubrovnik", "Istanbul", "Milan", "Vilnius", "Frankfurt"]
    idx = {c: i for i, c in enumerate(cities)}
    n_days = 22

    # Directed flight edges (as per problem statement)
    allowed = set()
    def add_bi(a, b):
        allowed.add((idx[a], idx[b]))
        allowed.add((idx[b], idx[a]))
    def add_uni(a, b):
        allowed.add((idx[a], idx[b]))

    # Add edges
    add_bi("Milan", "Frankfurt")
    add_bi("Split", "Frankfurt")
    add_bi("Milan", "Split")
    add_bi("Brussels", "Vilnius")
    add_bi("Brussels", "Helsinki")
    add_bi("Istanbul", "Brussels")
    add_bi("Milan", "Vilnius")
    add_bi("Brussels", "Milan")
    add_bi("Istanbul", "Helsinki")
    add_bi("Helsinki", "Vilnius")
    add_bi("Helsinki", "Dubrovnik")
    add_bi("Split", "Vilnius")
    add_uni("Dubrovnik", "Istanbul")       # one-way
    add_bi("Istanbul", "Milan")
    add_bi("Helsinki", "Frankfurt")
    add_bi("Istanbul", "Vilnius")
    add_bi("Split", "Helsinki")
    add_bi("Milan", "Helsinki")
    add_bi("Istanbul", "Frankfurt")
    add_uni("Brussels", "Frankfurt")       # one-way
    add_bi("Dubrovnik", "Frankfurt")
    add_bi("Frankfurt", "Vilnius")

    # Targets per city
    target_days = {
        "Brussels": 3,
        "Helsinki": 3,
        "Split": 4,
        "Dubrovnik": 2,
        "Istanbul": 5,
        "Milan": 4,
        "Vilnius": 5,
        "Frankfurt": 3,
    }

    # Decision variables: city for each day (0..len(cities)-1)
    day_city = [Int(f"day_{d+1}") for d in range(n_days)]
    s = Solver()

    # Domain constraints
    for d in range(n_days):
        s.add(And(day_city[d] >= 0, day_city[d] < len(cities)))

    # Direct-flight or same-city adjacency constraints
    for d in range(n_days - 1):
        same_city = day_city[d+1] == day_city[d]
        allowed_transitions = [And(day_city[d] == i, day_city[d+1] == j) for (i, j) in allowed]
        s.add(Or(same_city, Or(allowed_transitions)))

    # Presence definition:
    # A city X is considered "present" on day d if:
    # - day_city[d] == X, or
    # - (d < n_days-1 and day_city[d] != day_city[d+1] and day_city[d+1] == X)
    # This matches: flight on day d from A to B counts for both A and B on day d.
    def presence_expr(city_idx, d):
        if d < n_days - 1:
            return Or(day_city[d] == city_idx,
                      And(day_city[d] != day_city[d+1], day_city[d+1] == city_idx))
        else:
            return day_city[d] == city_idx

    # Hard requirement windows:
    # Days 1-5: must be present in Istanbul (attend show)
    for d in range(0, 5):
        s.add(presence_expr(idx["Istanbul"], d))

    # Frankfurt wedding: present on days 16-18
    for d in range(15, 18):
        s.add(presence_expr(idx["Frankfurt"], d))

    # Vilnius workshop: present on days 18-22
    for d in range(17, 22):
        s.add(presence_expr(idx["Vilnius"], d))

    # Exact days per city
    for cname, t in target_days.items():
        ci = idx[cname]
        pres_bools = [presence_expr(ci, d) for d in range(n_days)]
        s.add(Sum([If(pb, 1, 0) for pb in pres_bools]) == t)

    # Optional: Fix Istanbul to be the assigned city for days 1-5 (stronger than presence; respects the show)
    for d in range(0, 5):
        s.add(day_city[d] == idx["Istanbul"])

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found with given constraints.")

    m = s.model()
    itinerary = []
    for d in range(n_days):
        cidx = m[day_city[d]].as_long()
        itinerary.append({"day": d+1, "city": cities[cidx]})

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_itinerary()
# Requires: z3-solver
# pip install z3-solver
from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = [
        "Reykjavik",
        "Riga",
        "Oslo",
        "Lyon",
        "Dubrovnik",
        "Madrid",
        "Warsaw",
        "London",
    ]
    idx = {c: i for i, c in enumerate(cities)}

    # Directed edges for direct flights.
    # "and" pairs are bidirectional; the one explicit "from" is directional.
    edges = set()

    def add_and(a, b):
        edges.add((idx[a], idx[b]))
        edges.add((idx[b], idx[a]))

    def add_from(a, b):
        edges.add((idx[a], idx[b]))

    # Given direct flights list:
    add_and("Warsaw", "Reykjavik")
    add_and("Oslo", "Madrid")
    add_and("Warsaw", "Riga")
    add_and("Lyon", "London")
    add_and("Madrid", "London")
    add_and("Warsaw", "London")
    add_from("Reykjavik", "Madrid")
    add_and("Warsaw", "Oslo")
    add_and("Oslo", "Dubrovnik")
    add_and("Oslo", "Reykjavik")
    add_and("Riga", "Oslo")
    add_and("Oslo", "Lyon")
    add_and("Oslo", "London")
    add_and("London", "Reykjavik")
    add_and("Warsaw", "Madrid")
    add_and("Madrid", "Lyon")
    add_and("Dubrovnik", "Madrid")

    days = 18
    n_cities = len(cities)

    # Duration requirements (presence days, including flight days)
    required = {
        "Reykjavik": 4,
        "Riga": 2,
        "Oslo": 3,
        "Lyon": 5,
        "Dubrovnik": 2,
        "Madrid": 2,
        "Warsaw": 4,
        "London": 3,
    }

    # Decision variables: city of each day (0..n_cities-1)
    day_city = [Int(f"day_{d+1}") for d in range(days)]

    s = Optimize()

    for d in range(days):
        s.add(Or([day_city[d] == i for i in range(n_cities)]))

    # Movement constraint: if you change cities between days d and d+1, it must be along a direct flight.
    for d in range(1, days):
        change_ok = Or([And(day_city[d-1] == a, day_city[d] == b) for (a, b) in edges])
        s.add(Or(day_city[d] == day_city[d-1], change_ok))

    # Presence logic:
    # A city c is "present" on day d if:
    # - day_city[d] == c (you are there that day), OR
    # - d > 0 AND day_city[d-1] == c AND day_city[d] != day_city[d-1] (you depart from c on day d)
    def present_bool(c, d):
        if d == 0:
            return day_city[d] == c
        else:
            return Or(day_city[d] == c, And(day_city[d-1] == c, day_city[d] != day_city[d-1]))

    # Enforce presence counts
    for c_name, req in required.items():
        c = idx[c_name]
        count = Sum([If(present_bool(c, d), 1, 0) for d in range(days)])
        s.add(count == req)

    # Meeting in Riga between day 4 and day 5 (1-indexed), i.e., day indices 3 or 4 (0-indexed)
    riga = idx["Riga"]
    cond_riga_day4 = present_bool(riga, 3)
    cond_riga_day5 = present_bool(riga, 4)
    s.add(Or(cond_riga_day4, cond_riga_day5))

    # Wedding in Dubrovnik between day 7 and day 8 (1-indexed), i.e., day indices 6 or 7 (0-indexed)
    dbv = idx["Dubrovnik"]
    cond_dbv_day7 = present_bool(dbv, 6)
    cond_dbv_day8 = present_bool(dbv, 7)
    s.add(Or(cond_dbv_day7, cond_dbv_day8))

    # (Optional) Encourage fewer arbitrary changes: not necessary due to exact presence sums,
    # but we can still keep model simple without extra optimization.

    if s.check() != sat:
        raise RuntimeError("No valid itinerary found under given constraints.")

    m = s.model()
    itinerary = []
    for d in range(days):
        c = m[day_city[d]].as_long()
        itinerary.append({"day": d + 1, "city": cities[c]})

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    solve_itinerary()
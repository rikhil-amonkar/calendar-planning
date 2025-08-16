# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json

def solve_itinerary():
    days = range(1, 26)

    cities = [
        "Lyon",
        "Valencia",
        "Seville",
        "Paris",
        "Prague",
        "Oslo",
        "Tallinn",
        "Nice",
        "Mykonos",
        "Lisbon",
    ]
    idx = {c: i for i, c in enumerate(cities)}

    # Desired total days (counting rule with flight days counting for both)
    desired = {
        "Valencia": 2,
        "Oslo": 3,
        "Lyon": 4,
        "Prague": 3,
        "Paris": 4,
        "Nice": 4,
        "Seville": 5,
        "Tallinn": 2,
        "Mykonos": 5,
        "Lisbon": 2,
    }

    # Direct flight pairs (undirected)
    direct_pairs = [
        ("Lisbon", "Paris"),
        ("Lyon", "Nice"),
        ("Tallinn", "Oslo"),
        ("Prague", "Lyon"),
        ("Paris", "Oslo"),
        ("Lisbon", "Seville"),
        ("Prague", "Lisbon"),
        ("Oslo", "Nice"),
        ("Valencia", "Paris"),
        ("Valencia", "Lisbon"),
        ("Paris", "Nice"),
        ("Nice", "Mykonos"),
        ("Paris", "Lyon"),
        ("Valencia", "Lyon"),
        ("Prague", "Oslo"),
        ("Prague", "Paris"),
        ("Seville", "Paris"),
        ("Oslo", "Lyon"),
        ("Prague", "Valencia"),
        ("Lisbon", "Nice"),
        ("Lisbon", "Oslo"),
        ("Valencia", "Seville"),
        ("Lisbon", "Lyon"),
        ("Paris", "Tallinn"),
        ("Prague", "Tallinn"),
    ]
    allowed = set()
    for a, b in direct_pairs:
        allowed.add((idx[a], idx[b]))
        allowed.add((idx[b], idx[a]))

    # Z3 variables
    n_cities = len(cities)
    city_of_day = [Int(f"city_{d}") for d in days]  # city index at end of day d

    s = Solver()

    # Domain constraints
    for d in days:
        s.add(And(city_of_day[d - 1] >= 0, city_of_day[d - 1] < n_cities))

    # Change flags for d >= 2
    change = [Bool(f"chg_{d}") if d >= 2 else BoolVal(False) for d in days]
    for d in days:
        if d >= 2:
            s.add(change[d - 1] == (city_of_day[d - 1] != city_of_day[d - 2]))

    # Direct flight constraints: if change on day d, must be an allowed pair
    for d in days:
        if d >= 2:
            conds = [And(city_of_day[d - 2] == a, city_of_day[d - 1] == b) for (a, b) in allowed]
            s.add(Or(Not(change[d - 1]), Or(conds)))

    # v[city][day]: True if the city is counted on day (either end-of-day city,
    # or previous-day city if a change happens on this day)
    v = [[Bool(f"v_{c}_{d}") for d in days] for c in range(n_cities)]
    for d in days:
        for c in range(n_cities):
            if d == 1:
                s.add(v[c][d - 1] == (city_of_day[d - 1] == c))
            else:
                s.add(
                    v[c][d - 1]
                    == Or(
                        city_of_day[d - 1] == c,
                        And(change[d - 1], city_of_day[d - 2] == c),
                    )
                )

    # Duration constraints: exact desired counts
    for cname, cnt in desired.items():
        c = idx[cname]
        s.add(Sum([If(v[c][d - 1], 1, 0) for d in days]) == cnt)

    # Event constraints:
    # - Be in Valencia between day 3 and day 4 (at least one of those days counts for Valencia)
    s.add(Or(v[idx["Valencia"]][3 - 1], v[idx["Valencia"]][4 - 1]))

    # - Oslo meet between day 13 and day 15 (at least one day counts for Oslo)
    s.add(Or(v[idx["Oslo"]][13 - 1], v[idx["Oslo"]][14 - 1], v[idx["Oslo"]][15 - 1]))

    # - Seville annual show days 5..9: must count Seville on each of these days
    for d in range(5, 10):
        s.add(v[idx["Seville"]][d - 1])

    # - Mykonos wedding days 21..25: must count Mykonos on each of these days
    for d in range(21, 26):
        s.add(v[idx["Mykonos"]][d - 1])

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    m = s.model()
    itinerary = []
    for d in days:
        c_idx = m[city_of_day[d - 1]].as_long()
        itinerary.append({"day": d, "city": cities[c_idx]})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False, indent=2))
import json
from z3 import *

def main():
    # Define cities and indices
    cities = [
        "Rome",
        "Mykonos",
        "Lisbon",
        "Frankfurt",
        "Nice",
        "Stuttgart",
        "Venice",
        "Dublin",
        "Bucharest",
        "Seville"
    ]
    n = len(cities)
    city_to_idx = {c: i for i, c in enumerate(cities)}

    # Durations per city
    durations = {
        "Rome": 3,
        "Mykonos": 2,
        "Lisbon": 2,
        "Frankfurt": 5,
        "Nice": 3,
        "Stuttgart": 4,
        "Venice": 4,
        "Dublin": 2,
        "Bucharest": 2,
        "Seville": 5
    }
    durations_list = [durations[c] for c in cities]

    # Direct flight pairs (undirected)
    flight_pairs = [
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
        ("Venice", "Nice"),
        ("Rome", "Seville"),
        ("Frankfurt", "Rome"),
        ("Nice", "Dublin"),
        ("Rome", "Bucharest"),
        ("Frankfurt", "Dublin"),
        ("Rome", "Dublin"),
        ("Venice", "Dublin"),
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
    # Build adjacency matrix
    adj = [[False]*n for _ in range(n)]
    for a,b in flight_pairs:
        ia, ib = city_to_idx[a], city_to_idx[b]
        adj[ia][ib] = True
        adj[ib][ia] = True

    # SMT variables
    # Position -> city index (permutation of 0..9)
    pos_city = [Int(f"city_at_pos_{i}") for i in range(n)]
    # Start and end day for each position (1-based days)
    start_day = [Int(f"start_{i}") for i in range(n)]
    end_day = [Int(f"end_{i}") for i in range(n)]

    s = Solver()

    # Domain constraints for city indices
    for i in range(n):
        s.add(And(pos_city[i] >= 0, pos_city[i] < n))

    # All cities exactly once
    s.add(Distinct(pos_city))

    # Helper: duration expression for city at each position
    def dur_expr(city_var):
        expr = None
        for idx in range(n):
            cond = (city_var == idx)
            val = durations_list[idx]
            expr = If(cond, val, expr) if expr is not None else If(cond, val, 0)
        return expr

    # Timeline constraints with overlap on travel days
    # Day 1..23 total unique days, with 10 cities and 9 overlaps
    s.add(start_day[0] == 1)
    for i in range(n):
        Li = dur_expr(pos_city[i])
        s.add(end_day[i] == start_day[i] + Li - 1)
        s.add(start_day[i] >= 1)
        s.add(end_day[i] >= 1)
        if i < n-1:
            # Next start equals current end (overlap on travel day)
            s.add(start_day[i+1] == end_day[i])
            # Direct flight between consecutive cities
            ors = []
            for a in range(n):
                for b in range(n):
                    if adj[a][b]:
                        ors.append(And(pos_city[i] == a, pos_city[i+1] == b))
            s.add(Or(*ors))
    # End on Day 23
    s.add(end_day[n-1] == 23)

    # City-specific day constraints
    # Mykonos: exactly days 10-11 (2 days) and present between day 10 and 11
    MYK = city_to_idx["Mykonos"]
    for i in range(n):
        s.add(Implies(pos_city[i] == MYK, And(start_day[i] == 10, end_day[i] == 11)))

    # Seville: must include day 13 and day 17; with 5 days, this fixes start=13, end=17
    SEV = city_to_idx["Seville"]
    for i in range(n):
        s.add(Implies(pos_city[i] == SEV, And(start_day[i] == 13, end_day[i] == 17)))

    # Frankfurt: attend wedding between day 1 and day 5 => be in Frankfurt on some day in [1,5]
    FRA = city_to_idx["Frankfurt"]
    for i in range(n):
        s.add(Implies(pos_city[i] == FRA, start_day[i] <= 5))

    # Durations fixed per city (implicitly enforced by dur_expr), but ensure sum consistency if desired
    # Not necessary, as end_day[n-1]==23 together with overlap recurrence ensures total days 23.

    if s.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = s.model()

    # Extract itinerary
    itinerary = []
    for i in range(n):
        city_idx = m.evaluate(pos_city[i]).as_long()
        st = m.evaluate(start_day[i]).as_long()
        en = m.evaluate(end_day[i]).as_long()
        itinerary.append({
            "day_range": f"Day {st}-{en}",
            "place": cities[city_idx]
        })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
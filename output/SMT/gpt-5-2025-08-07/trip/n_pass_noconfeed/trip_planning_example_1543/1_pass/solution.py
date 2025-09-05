import json
from z3 import *

def solve_itinerary():
    # Define cities and indices
    cities = [
        "Prague", "Warsaw", "Dublin", "Athens", "Vilnius",
        "Porto", "London", "Seville", "Lisbon", "Dubrovnik"
    ]
    city_to_id = {c: i for i, c in enumerate(cities)}

    # Durations for each city
    durations = {
        "Prague": 3,
        "Warsaw": 4,
        "Dublin": 3,
        "Athens": 3,
        "Vilnius": 4,
        "Porto": 5,
        "London": 3,
        "Seville": 2,
        "Lisbon": 5,
        "Dubrovnik": 3
    }
    dur_by_id = {city_to_id[k]: v for k, v in durations.items()}

    # Allowed direct flights (undirected)
    flight_pairs = [
        ("Warsaw", "Vilnius"),
        ("Prague", "Athens"),
        ("London", "Lisbon"),
        ("Lisbon", "Porto"),
        ("Prague", "Lisbon"),
        ("London", "Dublin"),
        ("Athens", "Vilnius"),
        ("Athens", "Dublin"),
        ("Prague", "London"),
        ("London", "Warsaw"),
        ("Dublin", "Seville"),
        ("Seville", "Porto"),
        ("Lisbon", "Athens"),
        ("Dublin", "Porto"),
        ("Athens", "Warsaw"),
        ("Lisbon", "Warsaw"),
        ("Porto", "Warsaw"),
        ("Prague", "Warsaw"),
        ("Prague", "Dublin"),
        ("Athens", "Dubrovnik"),
        ("Lisbon", "Dublin"),
        ("Dubrovnik", "Dublin"),
        ("Lisbon", "Seville"),
        ("London", "Athens"),
    ]
    edges = set()
    for a, b in flight_pairs:
        ai, bi = city_to_id[a], city_to_id[b]
        edges.add((ai, bi))
        edges.add((bi, ai))

    n = 10
    total_days = 26

    # Z3 variables
    pos_city = [Int(f"city_at_pos_{p}") for p in range(n)]
    start = [Int(f"start_{p}") for p in range(n)]
    end = [Int(f"end_{p}") for p in range(n)]

    s = Solver()

    # Domain for cities and all-different (visit each exactly once)
    for p in range(n):
        s.add(And(pos_city[p] >= 0, pos_city[p] < n))
    s.add(Distinct(*pos_city))

    # Day ranges for segments
    for p in range(n):
        s.add(And(start[p] >= 1, start[p] <= total_days))
        s.add(And(end[p] >= 1, end[p] <= total_days))

    # Duration constraint: end[p] = start[p] + duration(city_at_pos[p]) - 1
    for p in range(n):
        dur_expr = Sum([If(pos_city[p] == cid, dur_by_id[cid], 0) for cid in range(n)])
        s.add(end[p] == start[p] + dur_expr - 1)

    # Chain the segments with 1-day overlap flights and cover exactly Day 1..26
    s.add(start[0] == 1)
    for p in range(n - 1):
        s.add(start[p + 1] == end[p])
    s.add(end[n - 1] == total_days)

    # Direct flight constraint between consecutive cities
    for p in range(n - 1):
        allowed_edges = []
        for (a, b) in edges:
            allowed_edges.append(And(pos_city[p] == a, pos_city[p + 1] == b))
        s.add(Or(*allowed_edges))

    # Helper to get city interval exprs
    def city_interval_expr(city_name):
        cid = city_to_id[city_name]
        s_expr = Sum([If(pos_city[p] == cid, start[p], 0) for p in range(n)])
        e_expr = Sum([If(pos_city[p] == cid, end[p], 0) for p in range(n)])
        return s_expr, e_expr

    # Window intersection constraints (must be present >=1 day in these ranges)
    # Workshop in Prague between day 1 and 3
    s_prague, e_prague = city_interval_expr("Prague")
    s.add(s_prague <= 3)
    s.add(e_prague >= 1)

    # Wedding in London between day 3 and 5
    s_london, e_london = city_interval_expr("London")
    s.add(s_london <= 5)
    s.add(e_london >= 3)

    # Relatives in Lisbon between day 5 and 9
    s_lisbon, e_lisbon = city_interval_expr("Lisbon")
    s.add(s_lisbon <= 9)
    s.add(e_lisbon >= 5)

    # Conference in Porto between day 16 and 20
    s_porto, e_porto = city_interval_expr("Porto")
    s.add(s_porto <= 20)
    s.add(e_porto >= 16)

    # Friends in Warsaw between day 20 and 23
    s_warsaw, e_warsaw = city_interval_expr("Warsaw")
    s.add(s_warsaw <= 23)
    s.add(e_warsaw >= 20)

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found with given constraints.")
    m = s.model()

    # Extract itinerary
    itinerary = []
    for p in range(n):
        cid = m[pos_city[p]].as_long()
        st = m[start[p]].as_long()
        en = m[end[p]].as_long()
        itinerary.append({"day_range": f"Day {st}-{en}", "place": cities[cid]})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False))
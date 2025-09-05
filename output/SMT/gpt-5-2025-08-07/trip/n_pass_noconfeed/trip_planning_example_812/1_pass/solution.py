import json
from z3 import *

def main():
    # Define cities
    cities = ["Paris", "Florence", "Vienna", "Porto", "Munich", "Nice", "Warsaw"]
    city_to_idx = {c: i for i, c in enumerate(cities)}
    P, F, V, PO, M, N, W = (city_to_idx[c] for c in cities)

    # Trip parameters
    total_days = 20

    # Duration requirements per city (days of presence; flights count for both cities on that day)
    required_days = {
        P: 5,   # Paris
        F: 3,   # Florence
        V: 2,   # Vienna
        PO: 3,  # Porto
        M: 5,   # Munich
        N: 5,   # Nice
        W: 3,   # Warsaw
    }

    # Must-be-in-city day ranges (inclusive)
    must_in_city = {
        PO: [(1, 3)],   # Workshop in Porto between day 1 and 3
        W:  [(13, 15)], # Wedding in Warsaw between day 13 and 15
        V:  [(19, 20)]  # Visit relatives in Vienna between day 19 and 20
    }

    # Build allowed direct flights graph (directed edges)
    # "A and B" => both directions; "from X to Y" => only X->Y
    undirected_pairs = [
        ("Florence", "Vienna"),
        ("Paris", "Warsaw"),
        ("Munich", "Vienna"),
        ("Porto", "Vienna"),
        ("Warsaw", "Vienna"),
        ("Munich", "Warsaw"),
        ("Munich", "Nice"),
        ("Paris", "Florence"),
        ("Warsaw", "Nice"),
        ("Porto", "Munich"),
        ("Porto", "Nice"),
        ("Paris", "Vienna"),
        ("Nice", "Vienna"),
        ("Porto", "Paris"),
        ("Paris", "Nice"),
        ("Paris", "Munich"),
        ("Porto", "Warsaw"),
    ]
    directed_pairs = [
        ("Florence", "Munich")  # from Florence to Munich
    ]

    allowed_pairs = set()
    for a, b in undirected_pairs:
        ai, bi = city_to_idx[a], city_to_idx[b]
        allowed_pairs.add((ai, bi))
        allowed_pairs.add((bi, ai))
    for a, b in directed_pairs:
        ai, bi = city_to_idx[a], city_to_idx[b]
        allowed_pairs.add((ai, bi))

    # Z3 setup
    opt = Optimize()

    # Variables
    # City at end of each day
    end_city = [Int(f"end_{d}") for d in range(1, total_days + 1)]
    # City at start of day 1 (before any flights)
    start0 = Int("start0")

    # Domains
    all_vars = [start0] + end_city
    for v in all_vars:
        opt.add(And(v >= 0, v < len(cities)))

    # Start city per day expression
    start_city = []
    for d in range(1, total_days + 1):
        if d == 1:
            start_city.append(start0)
        else:
            start_city.append(end_city[d - 2])

    # Flight day booleans and adjacency constraints
    flight_bools = []
    for d in range(total_days):
        sd = start_city[d]
        ed = end_city[d]
        flight = Bool(f"flight_{d+1}")
        opt.add(flight == (sd != ed))
        flight_bools.append(flight)

        # If a flight occurs, it must be along an allowed direct route
        # Or(no flight) or (sd, ed) in allowed_pairs
        allowed_cases = [And(sd == a, ed == b) for (a, b) in allowed_pairs]
        opt.add(Or(Not(flight), Or(allowed_cases)))

    # Presence booleans per city per day: present if city is at day's start or end
    present = {}
    for c in range(len(cities)):
        present[c] = []
        for d in range(total_days):
            sd = start_city[d]
            ed = end_city[d]
            present_cd = Bool(f"present_{cities[c]}_{d+1}")
            opt.add(present_cd == Or(sd == c, ed == c))
            present[c].append(present_cd)

    # Duration constraints per city
    for c, req in required_days.items():
        opt.add(Sum([If(present[c][d], 1, 0) for d in range(total_days)]) == req)

    # Must-be-in-city day-range constraints
    for c, ranges in must_in_city.items():
        for lo, hi in ranges:
            for d in range(lo - 1, hi):
                opt.add(present[c][d])

    # Exclude Vienna presence before day 19 (helpful pruning; consistent with exact 2 days on 19-20)
    for d in range(0, 18):
        opt.add(Not(present[V][d]))

    # Flights objective: minimize number of flight days (each flight day gives double presence)
    # Theoretical lower bound is (sum(required_days) - total_days) == 6; Optimize will seek minimal feasible.
    total_flights = Sum([If(flight_bools[d], 1, 0) for d in range(total_days)])
    opt.minimize(total_flights)

    # Solve
    if opt.check() != sat:
        # If for some reason Optimize can't find sat, fallback to Solver
        s = Solver()
        for c in opt.assertions():
            s.add(c)
        if s.check() != sat:
            # Should not happen; but output empty to conform
            print(json.dumps({"itinerary": []}))
            return
        m = s.model()
    else:
        m = opt.model()

    # Extract solution
    end_seq = [m.evaluate(end_city[d]).as_long() for d in range(total_days)]

    # Build itinerary as contiguous segments by end-city
    itinerary = []
    seg_start = 1
    current_city = end_seq[0]
    for d in range(2, total_days + 1):
        if end_seq[d - 1] != current_city:
            itinerary.append({
                "day_range": f"Day {seg_start}-{d-1}",
                "place": cities[current_city]
            })
            seg_start = d
            current_city = end_seq[d - 1]
    # Last segment
    itinerary.append({
        "day_range": f"Day {seg_start}-{total_days}",
        "place": cities[current_city]
    })

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
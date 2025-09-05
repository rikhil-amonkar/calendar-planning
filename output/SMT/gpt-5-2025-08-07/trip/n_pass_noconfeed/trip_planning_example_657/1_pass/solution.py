import json
from z3 import *

def main():
    # Constants
    days = list(range(1, 17))  # Day 1..16

    # Cities and indices
    cities = [
        "Frankfurt",  # 0
        "Manchester", # 1
        "Valencia",   # 2
        "Naples",     # 3
        "Oslo",       # 4
        "Vilnius"     # 5
    ]
    city_idx = {name: idx for idx, name in enumerate(cities)}

    # Required total presence (days counted with rule: flight day counts for both origin and destination)
    required_days = {
        "Frankfurt": 4,
        "Manchester": 4,
        "Valencia": 4,
        "Naples": 4,
        "Oslo": 3,
        "Vilnius": 2
    }

    # Direct flight edges (undirected)
    direct_pairs = set()
    def add_edge(a, b):
        direct_pairs.add((city_idx[a], city_idx[b]))
        direct_pairs.add((city_idx[b], city_idx[a]))

    add_edge("Valencia", "Frankfurt")
    add_edge("Manchester", "Frankfurt")
    add_edge("Naples", "Manchester")
    add_edge("Naples", "Frankfurt")
    add_edge("Naples", "Oslo")
    add_edge("Oslo", "Frankfurt")
    add_edge("Vilnius", "Frankfurt")
    add_edge("Oslo", "Vilnius")
    add_edge("Manchester", "Oslo")
    add_edge("Valencia", "Naples")

    # Z3 variables
    city_start = {d: Int(f"city_start_{d}") for d in days}
    city_end   = {d: Int(f"city_end_{d}")   for d in days}
    flight_day = {d: Bool(f"flight_day_{d}") for d in days}

    s = Optimize()

    # Domains
    for d in days:
        s.add(And(city_start[d] >= 0, city_start[d] < len(cities)))
        s.add(And(city_end[d]   >= 0, city_end[d]   < len(cities)))

    # Continuity: start of day d equals end of previous day (for d>1)
    for d in days:
        if d > 1:
            s.add(city_start[d] == city_end[d-1])

    # Flight logic and adjacency on flight days
    def adjacency_expr(a, b):
        # a, b are Int city indices
        clauses = []
        for (i, j) in direct_pairs:
            clauses.append(And(a == i, b == j))
        return Or(clauses) if clauses else False

    for d in days:
        # If no flight: stay in same city; If flight: move to a different, directly connected city
        s.add(
            Or(
                And(Not(flight_day[d]), city_end[d] == city_start[d]),
                And(flight_day[d], city_end[d] != city_start[d], adjacency_expr(city_start[d], city_end[d]))
            )
        )

    # Presence expression: present in city c on day d if end in c OR (flight and start in c)
    def present_expr(d, c):
        return Or(city_end[d] == c, And(flight_day[d], city_start[d] == c))

    # Duration constraints per city
    for name, req in required_days.items():
        c = city_idx[name]
        count_terms = []
        for d in days:
            # If present on day d in city c then +1
            count_terms.append(If(present_expr(d, c), 1, 0))
        s.add(Sum(count_terms) == req)

    # Event constraints:
    # - Frankfurt show: present on days 13..16
    for d in range(13, 17):
        s.add(present_expr(d, city_idx["Frankfurt"]))
    # - Wedding in Vilnius between day 12 and 13: present on both day 12 and day 13 in Vilnius
    s.add(present_expr(12, city_idx["Vilnius"]))
    s.add(present_expr(13, city_idx["Vilnius"]))

    # Optional: minimize number of flights (yields a simpler itinerary; also aligns with totals)
    total_flights = Sum([If(flight_day[d], 1, 0) for d in days])
    s.minimize(total_flights)

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": [], "status": "unsat"}))
        return
    m = s.model()

    # Extract model values
    model_city_start = {d: m.eval(city_start[d]).as_long() for d in days}
    model_city_end   = {d: m.eval(city_end[d]).as_long() for d in days}
    model_flight     = {d: is_true(m.eval(flight_day[d])) for d in days}

    # Compute presence per day per city
    presence = {d: set() for d in days}
    for d in days:
        presence[d].add(model_city_end[d])
        if model_flight[d]:
            presence[d].add(model_city_start[d])

    # Build contiguous ranges of presence for each city
    ranges = []
    for c_idx, cname in enumerate(cities):
        in_run = False
        run_start = None
        for d in days:
            is_present = c_idx in presence[d]
            if is_present and not in_run:
                in_run = True
                run_start = d
            elif not is_present and in_run:
                ranges.append((run_start, d - 1, cname))
                in_run = False
                run_start = None
        if in_run:
            ranges.append((run_start, days[-1], cname))

    # Sort ranges by start day
    ranges.sort(key=lambda x: (x[0], x[1]))

    # Format output
    itinerary = []
    for start, end, place in ranges:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": place
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
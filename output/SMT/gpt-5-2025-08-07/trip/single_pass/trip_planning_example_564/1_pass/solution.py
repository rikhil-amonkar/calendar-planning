from z3 import *
import json

def solve_itinerary():
    # Constants
    days_total = 16
    cities = ["Seville", "Rome", "Istanbul", "Naples", "Santorini"]
    city_idx = {c: i for i, c in enumerate(cities)}

    # Required total days per city (counting flight days for both cities)
    req_days = {
        city_idx["Istanbul"]: 2,
        city_idx["Rome"]: 3,
        city_idx["Seville"]: 4,
        city_idx["Naples"]: 7,
        city_idx["Santorini"]: 4,
    }

    # Allowed direct flights (undirected)
    allowed_edges = set()
    def add_edge(a, b):
        allowed_edges.add((city_idx[a], city_idx[b]))
        allowed_edges.add((city_idx[b], city_idx[a]))
    add_edge("Rome", "Santorini")
    add_edge("Seville", "Rome")
    add_edge("Istanbul", "Naples")
    add_edge("Naples", "Santorini")
    add_edge("Rome", "Naples")
    add_edge("Rome", "Istanbul")

    # Helper: select element from a list of Z3 expressions by an index (Int)
    def sel(arr, idx):
        expr = arr[0]
        for i in range(1, len(arr)):
            expr = If(idx == i, arr[i], expr)
        return expr

    # Z3 solver
    s = Solver()

    # Route as a permutation of the 5 cities, visited exactly once, in order
    ord_vars = [Int(f"ord_{i}") for i in range(5)]
    for v in ord_vars:
        s.add(v >= 0, v < 5)
    s.add(Distinct(*ord_vars))

    # Primary day lengths per segment (days assigned to the "origin" city on each day)
    Lprim = [Int(f"Lprim_{i}") for i in range(5)]

    # Compute Lprim[k] = req_days[ord[k]] - (1 if k>0 else 0)
    for k in range(5):
        terms = []
        for c in range(5):
            sub = 1 if k > 0 else 0
            terms.append(If(ord_vars[k] == c, req_days[c] - sub, 0))
        s.add(Lprim[k] == Sum(*terms))
        s.add(Lprim[k] >= 1)

    # Start/end days of primary segments (partition the 16 days)
    start = [Int(f"start_{i}") for i in range(5)]
    end = [Int(f"end_{i}") for i in range(5)]

    s.add(start[0] == 1)
    for k in range(5):
        s.add(end[k] == start[k] + Lprim[k] - 1)
        if k > 0:
            s.add(start[k] == end[k-1] + 1)

    s.add(end[4] == days_total)

    # Direct flight between consecutive cities in the route
    for k in range(4):
        allowed_opts = []
        for (a, b) in allowed_edges:
            allowed_opts.append(And(ord_vars[k] == a, ord_vars[k+1] == b))
        s.add(Or(*allowed_opts))

    # Constraints for Istanbul: must be in Istanbul on day 6 and 7 (2 days),
    # with the relatives visit "between day 6 and day 7" meaning Istanbul spans the boundary.
    # This is achieved by making day 6 the arrival day to Istanbul and day 7 its primary day.
    pos_ist = Int("pos_ist")
    s.add(Or([pos_ist == i for i in range(5)]))
    s.add(pos_ist > 0)  # not the first segment
    # Bind pos_ist to the position where the city is Istanbul
    for i in range(5):
        s.add(Implies(pos_ist == i, ord_vars[i] == city_idx["Istanbul"]))
    # The arrival day to the Istanbul segment is end[pos_ist - 1] == 6, and start[pos_ist] == 7
    s.add(sel(end, pos_ist - 1) == 6)
    s.add(sel(start, pos_ist) == 7)

    # Constraints for Santorini: must cover days 13-16 (wedding).
    # This is satisfied by making Santorini the last segment, with arrival on day 13.
    s.add(ord_vars[4] == city_idx["Santorini"])
    s.add(end[3] == 13)  # arrival to Santorini on day 13; primary days 14-16

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    m = s.model()

    # Extract route and day partitions
    ord_vals = [m.eval(ord_vars[i]).as_long() for i in range(5)]
    start_vals = [m.eval(start[i]).as_long() for i in range(5)]
    end_vals = [m.eval(end[i]).as_long() for i in range(5)]

    # Build day-to-city mapping based on primary days (no separate flight entries)
    itinerary = []
    for d in range(1, days_total + 1):
        # Find which segment k has primary day covering d
        city_for_d = None
        for k in range(5):
            if start_vals[k] <= d <= end_vals[k]:
                city_for_d = cities[ord_vals[k]]
                break
        if city_for_d is None:
            raise RuntimeError(f"Day {d} not assigned to any city (unexpected).")
        itinerary.append({"day": d, "city": city_for_d})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))
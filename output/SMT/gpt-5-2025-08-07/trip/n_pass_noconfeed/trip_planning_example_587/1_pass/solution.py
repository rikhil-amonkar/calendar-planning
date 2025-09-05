import json
from z3 import *

def main():
    # Cities and indices
    cities = ["Manchester", "Istanbul", "Venice", "Krakow", "Lyon"]
    city_to_idx = {name: i for i, name in enumerate(cities)}
    idx_to_city = {i: name for i, name in enumerate(cities)}

    # Constraints (input variables)
    total_days = 21
    required_days = {
        "Manchester": 3,
        "Istanbul": 7,
        "Venice": 7,
        "Krakow": 6,
        "Lyon": 2,
    }
    # Windows: inclusive day ranges
    wedding_city = "Manchester"
    wedding_window = (1, 3)  # between day 1 and day 3
    workshop_city = "Venice"
    workshop_window = (3, 9)  # between day 3 and day 9

    # Direct flights (undirected)
    direct_flights = {
        ("Manchester", "Venice"),
        ("Manchester", "Istanbul"),
        ("Venice", "Istanbul"),
        ("Istanbul", "Krakow"),
        ("Venice", "Lyon"),
        ("Lyon", "Istanbul"),
        ("Manchester", "Krakow"),
    }
    # Convert to directed adjacency set of index pairs
    adj = set()
    for a, b in direct_flights:
        ai, bi = city_to_idx[a], city_to_idx[b]
        adj.add((ai, bi))
        adj.add((bi, ai))

    # Z3 variables
    c1, c2, c3, c4, c5 = Ints('c1 c2 c3 c4 c5')  # order of visiting the 5 cities
    f1, f2, f3, f4 = Ints('f1 f2 f3 f4')         # flight days (4 flights)
    cpos = [c1, c2, c3, c4, c5]
    f = [f1, f2, f3, f4]

    s = Solver()

    # Domain: cities are indices 0..4 and all distinct (visit each exactly once)
    for ci in cpos:
        s.add(And(ci >= 0, ci <= 4))
    s.add(Distinct(cpos))

    # Flights days strictly increasing within trip days
    s.add(And(f1 >= 1, f4 <= total_days))
    s.add(f1 < f2, f2 < f3, f3 < f4)

    # Adjacency constraints for consecutive cities (direct flights only)
    def allowed_edge(x, y):
        return Or([And(x == a, y == b) for (a, b) in adj])

    s.add(allowed_edge(c1, c2))
    s.add(allowed_edge(c2, c3))
    s.add(allowed_edge(c3, c4))
    s.add(allowed_edge(c4, c5))

    # Durations per segment (inclusive intervals)
    # Intervals:
    # I1: [1,  f1]
    # I2: [f1, f2]
    # I3: [f2, f3]
    # I4: [f3, f4]
    # I5: [f4, total_days]
    dur1 = f1
    dur2 = f2 - f1 + 1
    dur3 = f3 - f2 + 1
    dur4 = f4 - f3 + 1
    dur5 = (total_days + 1) - f4  # 22 - f4 when total_days = 21

    # Durations assigned to each specific city by their segment
    def dur_for_city(city_idx):
        return (If(c1 == city_idx, dur1, 0) +
                If(c2 == city_idx, dur2, 0) +
                If(c3 == city_idx, dur3, 0) +
                If(c4 == city_idx, dur4, 0) +
                If(c5 == city_idx, dur5, 0))

    # Required durations per city
    for name, req in required_days.items():
        s.add(dur_for_city(city_to_idx[name]) == req)

    # Window intersection helper
    def intersects(lo, hi, L, U):
        # [lo,hi] intersects [L,U] iff lo <= U and L <= hi
        return And(lo <= U, L <= hi)

    # Presence windows for each segment
    lo1, hi1 = 1, f1
    lo2, hi2 = f1, f2
    lo3, hi3 = f2, f3
    lo4, hi4 = f3, f4
    lo5, hi5 = f4, total_days

    # Wedding in Manchester between wedding_window
    wL, wU = wedding_window
    man_idx = city_to_idx[wedding_city]
    wedding_ok = Or(
        And(c1 == man_idx, intersects(lo1, hi1, wL, wU)),
        And(c2 == man_idx, intersects(lo2, hi2, wL, wU)),
        And(c3 == man_idx, intersects(lo3, hi3, wL, wU)),
        And(c4 == man_idx, intersects(lo4, hi4, wL, wU)),
        And(c5 == man_idx, intersects(lo5, hi5, wL, wU))
    )
    s.add(wedding_ok)

    # Workshop in Venice between workshop_window
    wsL, wsU = workshop_window
    ven_idx = city_to_idx[workshop_city]
    workshop_ok = Or(
        And(c1 == ven_idx, intersects(lo1, hi1, wsL, wsU)),
        And(c2 == ven_idx, intersects(lo2, hi2, wsL, wsU)),
        And(c3 == ven_idx, intersects(lo3, hi3, wsL, wsU)),
        And(c4 == ven_idx, intersects(lo4, hi4, wsL, wsU)),
        And(c5 == ven_idx, intersects(lo5, hi5, wsL, wsU))
    )
    s.add(workshop_ok)

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = s.model()

    # Extract model values
    c_vals = [m.eval(ci).as_long() for ci in cpos]
    f_vals = [m.eval(fi).as_long() for fi in f]

    # Build itinerary
    intervals = [
        (1, f_vals[0]),
        (f_vals[0], f_vals[1]),
        (f_vals[1], f_vals[2]),
        (f_vals[2], f_vals[3]),
        (f_vals[3], total_days),
    ]
    itinerary = []
    for i, (start_day, end_day) in enumerate(intervals):
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": idx_to_city[c_vals[i]]
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
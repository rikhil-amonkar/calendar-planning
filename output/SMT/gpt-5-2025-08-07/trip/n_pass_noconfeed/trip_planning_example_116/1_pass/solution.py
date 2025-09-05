import json
from z3 import *

def solve_itinerary():
    # Input parameters
    total_days = 18
    cities = ["London", "Santorini", "Split"]
    required_days = {
        "London": 7,
        "Santorini": 7,
        "Split": 6
    }
    # Direct flight edges (bidirectional)
    direct_flights = {
        ("London", "Santorini"),
        ("Santorini", "London"),
        ("London", "Split"),
        ("Split", "London")
    }
    conference_city = "Santorini"
    conference_days = [12, 18]

    # Mappings
    city_to_idx = {c: i for i, c in enumerate(cities)}
    idx_to_city = {i: c for c, i in city_to_idx.items()}

    # Z3 variables
    T = total_days
    base = [Int(f"base_{d+1}") for d in range(T)]       # base city for day d (where you "sleep")
    to = [Int(f"to_{d+1}") for d in range(T)]           # if a flight occurs on day d, destination city; else equals base[d]
    fl = [Bool(f"fl_{d+1}") for d in range(T)]          # whether a flight occurs on day d

    s = Optimize()

    # Domain constraints
    for d in range(T):
        s.add(Or([base[d] == city_to_idx[c] for c in cities]))
        s.add(Or([to[d] == city_to_idx[c] for c in cities]))

    # Direct flight constraint helper
    def edge_allowed(a, b):
        conds = [And(a == city_to_idx[src], b == city_to_idx[dst]) for (src, dst) in direct_flights]
        return Or(*conds)

    # Flight logic and city transitions
    for d in range(T):
        # If flight occurs, it must be to a different city and via a direct edge
        s.add(Implies(fl[d], And(to[d] != base[d], edge_allowed(base[d], to[d]))))
        # If no flight, travel destination equals base (no movement)
        s.add(Implies(Not(fl[d]), to[d] == base[d]))

    # Next-day base city transition: day d+1 base is destination if flew on day d, else unchanged
    for d in range(T - 1):
        s.add(base[d + 1] == If(fl[d], to[d], base[d]))

    # Presence counts per city (present if base city equals or a flight brings you to that city on that day)
    for city_name, req in required_days.items():
        cidx = city_to_idx[city_name]
        presence = [
            If(Or(base[d] == cidx, And(fl[d], to[d] == cidx)), 1, 0)
            for d in range(T)
        ]
        s.add(Sum(presence) == req)

    # Conference day constraints: must be present in Santorini on specified days
    conf_idx = city_to_idx[conference_city]
    for day in conference_days:
        d = day - 1
        s.add(Or(base[d] == conf_idx, And(fl[d], to[d] == conf_idx)))

    # Objective: minimize number of flight days (and then tie-break by earliest flight days)
    total_flights = Sum([If(fl[d], 1, 0) for d in range(T)])
    s.minimize(total_flights)
    # Tie-breaker: prefer earlier flights by minimizing the sum of flight day indices
    s.minimize(Sum([If(fl[d], d + 1, 0) for d in range(T)]))

    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    m = s.model()

    # Extract model values
    base_vals = [m.eval(base[d]).as_long() for d in range(T)]
    to_vals = [m.eval(to[d]).as_long() for d in range(T)]
    fl_vals = [is_true(m.eval(fl[d])) for d in range(T)]

    # Build itinerary segments:
    # Segments include overlapping day on flight days (both end & start include the flight day)
    flights_days = [i + 1 for i, f in enumerate(fl_vals) if f]
    segments = []
    if T > 0:
        start_day = 1
        current_city = base_vals[0]
        for fday in flights_days:
            # Segment until flight day in current city
            segments.append((start_day, fday, current_city))
            # After flight, city changes to destination of that flight
            current_city = to_vals[fday - 1]
            start_day = fday
        # Final segment until end
        segments.append((start_day, T, current_city))

    # Format output
    itinerary = []
    for (a, b, cidx) in segments:
        itinerary.append({
            "day_range": f"Day {a}-{b}",
            "place": idx_to_city[cidx]
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    solve_itinerary()
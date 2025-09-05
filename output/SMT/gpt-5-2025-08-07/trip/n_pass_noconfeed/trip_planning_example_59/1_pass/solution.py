import json
from z3 import Solver, Int, And, Or, If, Distinct, sat

def solve_itinerary():
    # Input parameters
    num_days = 16
    cities = ["Bucharest", "Lyon", "Porto"]
    required_days = {"Bucharest": 7, "Lyon": 7, "Porto": 4}
    direct_routes = {("Bucharest", "Lyon"), ("Lyon", "Bucharest"), ("Lyon", "Porto"), ("Porto", "Lyon")}
    wedding_window = (1, 7)  # must be in Bucharest on at least one day in this inclusive range

    # Map cities to integer indices
    city_to_idx = {name: i for i, name in enumerate(cities)}
    idx_to_city = {i: name for name, i in city_to_idx.items()}

    # Z3 variables
    c1 = Int("c1")  # city index for segment 1 (days 1..d1 inclusive)
    c2 = Int("c2")  # city index for segment 2 (days d1..d2 inclusive)
    c3 = Int("c3")  # city index for segment 3 (days d2..num_days inclusive)
    d1 = Int("d1")  # first flight day (inclusive overlap)
    d2 = Int("d2")  # second flight day (inclusive overlap)

    dur = [Int(f"dur_{i}") for i in range(len(cities))]  # duration per city (counting overlap days)

    s = Solver()

    # Domain constraints
    s.add(And(c1 >= 0, c1 < len(cities)))
    s.add(And(c2 >= 0, c2 < len(cities)))
    s.add(And(c3 >= 0, c3 < len(cities)))
    s.add(Distinct(c1, c2, c3))

    s.add(And(d1 >= 1, d1 < d2, d2 <= num_days))

    # Only direct flights between segments (c1->c2) and (c2->c3)
    def allowed_pair(x, y):
        return Or([And(x == city_to_idx[a], y == city_to_idx[b]) for (a, b) in direct_routes])

    s.add(allowed_pair(c1, c2))
    s.add(allowed_pair(c2, c3))

    # Durations per city based on segment positions
    for i in range(len(cities)):
        s.add(dur[i] == If(c1 == i, d1, 0) +
                         If(c2 == i, d2 - d1 + 1, 0) +
                         If(c3 == i, num_days - d2 + 1, 0))
        s.add(dur[i] >= 1)

    # Required days per city
    for name, req in required_days.items():
        s.add(dur[city_to_idx[name]] == req)

    # Wedding constraint: in Bucharest on at least one day between day 1 and day 7 (inclusive)
    # With inclusive-overlap segments:
    # - If Bucharest is c1, it covers days 1..d1, so it intersects [1..7]
    # - If Bucharest is c2, its days are d1..d2, intersects [1..7] iff d1 <= 7
    # - If Bucharest is c3, its days are d2..num_days, intersects [1..7] iff d2 <= 7
    B_idx = city_to_idx["Bucharest"]
    s.add(Or(c1 == B_idx,
             And(c2 == B_idx, d1 <= wedding_window[1]),
             And(c3 == B_idx, d2 <= wedding_window[1])))

    result = {"itinerary": []}

    if s.check() == sat:
        m = s.model()
        c1_val = m[c1].as_long()
        c2_val = m[c2].as_long()
        c3_val = m[c3].as_long()
        d1_val = m[d1].as_long()
        d2_val = m[d2].as_long()

        itinerary = [
            {"day_range": f"Day 1-{d1_val}", "place": idx_to_city[c1_val]},
            {"day_range": f"Day {d1_val}-{d2_val}", "place": idx_to_city[c2_val]},
            {"day_range": f"Day {d2_val}-{num_days}", "place": idx_to_city[c3_val]},
        ]
        result["itinerary"] = itinerary
    else:
        # In case of unsatisfiable (should not happen with given constraints)
        result["itinerary"] = []

    return result

if __name__ == "__main__":
    output = solve_itinerary()
    print(json.dumps(output))
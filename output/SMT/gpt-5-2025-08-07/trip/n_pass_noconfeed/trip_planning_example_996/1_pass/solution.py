import json
from z3 import Solver, Ints, Int, And, Or, Distinct, Implies, sat

def main():
    # Input variables (trip constraints)
    total_days = 22
    cities = ["Valencia", "Riga", "Prague", "Mykonos", "Zurich", "Bucharest", "Nice"]
    durations = {
        "Valencia": 5,
        "Riga": 5,
        "Prague": 3,
        "Mykonos": 3,
        "Zurich": 5,
        "Bucharest": 5,
        "Nice": 2
    }

    # Special inclusion constraints (must cover these day ranges)
    special_inclusions = {
        "Mykonos": (1, 3),  # Wedding between day 1 and day 3 (inclusive)
        "Prague": (7, 9)    # Visit relatives between day 7 and day 9 (inclusive)
    }

    # Direct flight pairs (undirected)
    direct_pairs = [
        ("Mykonos", "Nice"),
        ("Mykonos", "Zurich"),
        ("Prague", "Bucharest"),
        ("Valencia", "Bucharest"),
        ("Zurich", "Prague"),
        ("Riga", "Nice"),
        ("Zurich", "Riga"),
        ("Zurich", "Bucharest"),
        ("Zurich", "Valencia"),
        ("Bucharest", "Riga"),
        ("Prague", "Riga"),
        ("Prague", "Valencia"),
        ("Zurich", "Nice"),
    ]

    # Map city to index
    city_to_idx = {c: i for i, c in enumerate(cities)}
    idx_to_city = {i: c for c, i in city_to_idx.items()}

    n_segments = len(cities)  # exactly 7 segments (one per city)

    # Create Z3 variables
    order = [Int(f"order_{i}") for i in range(n_segments)]     # permutation of city indices
    start = [Int(f"start_{i}") for i in range(n_segments)]     # start day of segment i
    end = [Int(f"end_{i}") for i in range(n_segments)]         # end day of segment i

    s = Solver()

    # Domain constraints for order and days
    for i in range(n_segments):
        s.add(And(order[i] >= 0, order[i] < n_segments))
        s.add(And(start[i] >= 1, end[i] >= start[i]))

    # All cities visited exactly once
    s.add(Distinct(order))

    # Duration constraints per segment depending on which city is assigned to the segment
    for i in range(n_segments):
        for city, dur in durations.items():
            c_idx = city_to_idx[city]
            s.add(Implies(order[i] == c_idx, end[i] - start[i] + 1 == dur))

    # Chain segments with 1-day overlap (flight day counts for both cities)
    s.add(start[0] == 1)
    for i in range(n_segments - 1):
        s.add(start[i + 1] == end[i])

    # End on the total_days
    s.add(end[-1] == total_days)

    # Special inclusion constraints (city must include specific day ranges)
    for city, (must_start_day, must_end_day) in special_inclusions.items():
        c_idx = city_to_idx[city]
        for i in range(n_segments):
            s.add(Implies(order[i] == c_idx, And(start[i] <= must_start_day, end[i] >= must_end_day)))

    # Direct flight adjacency constraints between consecutive segments
    allowed_pairs = set()
    for a, b in direct_pairs:
        ai, bi = city_to_idx[a], city_to_idx[b]
        allowed_pairs.add((ai, bi))
        allowed_pairs.add((bi, ai))
    for i in range(n_segments - 1):
        s.add(Or(*[And(order[i] == u, order[i + 1] == v) for (u, v) in allowed_pairs]))

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found with the given constraints."}))
        return

    m = s.model()

    # Extract solution
    itinerary = []
    for i in range(n_segments):
        city_idx = m.evaluate(order[i]).as_long()
        city_name = idx_to_city[city_idx]
        si = m.evaluate(start[i]).as_long()
        ei = m.evaluate(end[i]).as_long()
        itinerary.append({
            "day_range": f"Day {si}-{ei}",
            "place": city_name
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
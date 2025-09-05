import json
from z3 import *

def main():
    # Trip parameters
    total_days = 17
    cities = [
        "Frankfurt",
        "Dublin",
        "London",
        "Vilnius",
        "Stuttgart",
        "Seville",
        "Santorini",
    ]
    city_index = {c: i for i, c in enumerate(cities)}
    n = len(cities)

    # Required lengths per city (in days, counting flight overlap days toward both cities)
    durations = {
        "Seville": 5,
        "Vilnius": 3,
        "Santorini": 2,
        "London": 2,
        "Stuttgart": 3,
        "Dublin": 3,
        "Frankfurt": 5,
    }

    # Map durations to indices
    dur_by_idx = [0] * n
    for c, d in durations.items():
        dur_by_idx[city_index[c]] = d

    # Direct flights (bidirectional edges)
    direct_pairs = [
        ("Frankfurt", "Dublin"),
        ("Frankfurt", "London"),
        ("London", "Dublin"),
        ("Vilnius", "Frankfurt"),
        ("Frankfurt", "Stuttgart"),
        ("Dublin", "Seville"),
        ("London", "Santorini"),
        ("Stuttgart", "London"),
        ("Santorini", "Dublin"),
    ]
    allowed_pairs = set()
    for a, b in direct_pairs:
        ai = city_index[a]
        bi = city_index[b]
        allowed_pairs.add((ai, bi))
        allowed_pairs.add((bi, ai))
    allowed_pairs = list(allowed_pairs)

    # SMT variables
    order = [Int(f"order_{i}") for i in range(n)]  # permutation of cities
    s = [Int(f"s_{i}") for i in range(n)]          # start day for segment i
    e = [Int(f"e_{i}") for i in range(n)]          # end day for segment i

    solver = Solver()

    # Domain constraints for order
    for i in range(n):
        solver.add(And(order[i] >= 0, order[i] < n))
    solver.add(Distinct(order))  # permutation

    # Helper: piecewise duration for each segment i based on order[i]
    def duration_for(order_var):
        expr = None
        for idx in range(n):
            case = If(order_var == idx, dur_by_idx[idx], 0)
            expr = case if expr is None else expr + case
        return expr

    # Time chaining with overlap on travel days
    solver.add(s[0] == 1)
    for i in range(n):
        di = duration_for(order[i])
        solver.add(e[i] == s[i] + di - 1)
        solver.add(And(s[i] >= 1, s[i] <= total_days))
        solver.add(And(e[i] >= 1, e[i] <= total_days))
        if i < n - 1:
            # Next city starts on the same day current city ends (counts as flight day)
            solver.add(s[i+1] == e[i])

    # The last day must be exactly total_days
    solver.add(e[n - 1] == total_days)

    # Only take direct flights between consecutive cities
    for i in range(n - 1):
        # order[i] -> order[i+1] must be in allowed_pairs
        allowed = [And(order[i] == a, order[i+1] == b) for (a, b) in allowed_pairs]
        solver.add(Or(*allowed))

    # Helper: predicate for being in a city on a day d
    def in_city_on_day(city_idx, day):
        return Or(*[
            And(order[i] == city_idx, s[i] <= day, day <= e[i])
            for i in range(n)
        ])

    # Special constraints:
    # - Be in London on both day 9 and day 10
    london_idx = city_index["London"]
    solver.add(in_city_on_day(london_idx, 9))
    solver.add(in_city_on_day(london_idx, 10))

    # - Be in Stuttgart on at least one day in [7, 9]
    stuttgart_idx = city_index["Stuttgart"]
    solver.add(Or(in_city_on_day(stuttgart_idx, 7),
                  in_city_on_day(stuttgart_idx, 8),
                  in_city_on_day(stuttgart_idx, 9)))

    # Solve
    if solver.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found."}))
        return

    model = solver.model()

    # Build itinerary as ordered segments with day ranges
    itinerary = []
    for i in range(n):
        ci = model.eval(order[i]).as_long()
        start = model.eval(s[i]).as_long()
        end = model.eval(e[i]).as_long()
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": cities[ci]
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
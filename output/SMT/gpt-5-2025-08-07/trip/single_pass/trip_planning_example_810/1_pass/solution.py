from z3 import *
import json

def solve_itinerary():
    # Cities and indices
    cities = ["Berlin", "Barcelona", "Lyon", "Nice", "Stockholm", "Athens", "Vilnius"]
    city_to_idx = {c: i for i, c in enumerate(cities)}
    idx_to_city = {i: c for i, c in enumerate(cities)}

    # Stay requirements (days counted with flight-day double-count rule)
    required_days = {
        "Berlin": 3,
        "Nice": 5,
        "Athens": 5,
        "Stockholm": 5,
        "Barcelona": 2,
        "Vilnius": 4,
        "Lyon": 2,
    }

    # Direct flight connections (undirected)
    direct_pairs = [
        ("Lyon", "Nice"),
        ("Stockholm", "Athens"),
        ("Nice", "Athens"),
        ("Berlin", "Athens"),
        ("Berlin", "Nice"),
        ("Berlin", "Barcelona"),
        ("Berlin", "Vilnius"),
        ("Barcelona", "Nice"),
        ("Athens", "Vilnius"),
        ("Berlin", "Stockholm"),
        ("Nice", "Stockholm"),
        ("Barcelona", "Athens"),
        ("Barcelona", "Stockholm"),
        ("Barcelona", "Lyon"),
    ]
    # Build set of allowed transitions (both directions)
    allowed_transitions = set()
    for a, b in direct_pairs:
        ai, bi = city_to_idx[a], city_to_idx[b]
        allowed_transitions.add((ai, bi))
        allowed_transitions.add((bi, ai))

    N = 20  # total days

    # Variables: city on each day (ending city for that day)
    day_city = [Int(f"day_{d}") for d in range(1, N + 1)]

    s = Solver()

    # Domain constraints
    for d in range(N):
        s.add(And(day_city[d] >= 0, day_city[d] < len(cities)))

    # Helper: presence predicate for city c on day d (1-based index)
    def present_on_day(c_idx, d):
        # present if day_city[d] == c OR (d>1 and day_city[d-1] == c and flight occurs on day d)
        if d == 1:
            return day_city[0] == c_idx
        else:
            return Or(
                day_city[d - 1] == c_idx,
                And(day_city[d - 2] == c_idx, day_city[d - 1] != day_city[d - 2])
            )

    # Only direct flights between different cities (or stay in same city)
    for d in range(1, N):  # days 2..N (index d is day d+1)
        prev_c = day_city[d - 1]
        curr_c = day_city[d]
        # Either no flight (same city) or allowed transition
        s.add(
            Or(
                curr_c == prev_c,
                Or(*[And(prev_c == a, curr_c == b) for (a, b) in allowed_transitions])
            )
        )

    # Stay requirements per city with flight-day double-count rule
    for cname, req in required_days.items():
        cidx = city_to_idx[cname]
        total = Sum([If(present_on_day(cidx, d+1), 1, 0) for d in range(N)])
        s.add(total == req)

    # Conference in Berlin on Day 1 and Day 3
    s.add(present_on_day(city_to_idx["Berlin"], 1))
    s.add(present_on_day(city_to_idx["Berlin"], 3))

    # Workshop in Barcelona between day 3 and day 4 (present on day 3 or 4)
    s.add(Or(present_on_day(city_to_idx["Barcelona"], 3),
             present_on_day(city_to_idx["Barcelona"], 4)))

    # Wedding in Lyon between day 4 and day 5 (present on day 4 or 5)
    s.add(Or(present_on_day(city_to_idx["Lyon"], 4),
             present_on_day(city_to_idx["Lyon"], 5)))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No valid itinerary found")

    m = s.model()
    itinerary = []
    for d in range(N):
        city_idx = m[day_city[d]].as_long()
        itinerary.append({"day": d + 1, "city": idx_to_city[city_idx]})

    print(json.dumps({"itinerary": itinerary}, indent=2))


if __name__ == "__main__":
    solve_itinerary()
# Requires: z3-solver
# pip install z3-solver
from z3 import *
import json

def solve_itinerary():
    # Cities and required total "presence days" (including flight-day double counts)
    cities = ["Vienna", "Lyon", "Edinburgh", "Reykjavik", "Stuttgart", "Manchester", "Split", "Prague"]
    idx = {name: i for i, name in enumerate(cities)}

    required_days = {
        "Vienna": 4,
        "Lyon": 3,
        "Edinburgh": 4,
        "Reykjavik": 5,
        "Stuttgart": 5,
        "Manchester": 2,
        "Split": 5,
        "Prague": 4,
    }

    # Direct flight edges (undirected)
    undirected_edges = {
        ("Reykjavik", "Stuttgart"),
        ("Stuttgart", "Split"),
        ("Stuttgart", "Vienna"),
        ("Prague", "Manchester"),
        ("Edinburgh", "Prague"),
        ("Manchester", "Split"),
        ("Prague", "Vienna"),
        ("Vienna", "Manchester"),
        ("Prague", "Split"),
        ("Vienna", "Lyon"),
        ("Stuttgart", "Edinburgh"),
        ("Split", "Lyon"),
        ("Stuttgart", "Manchester"),
        ("Prague", "Lyon"),
        ("Reykjavik", "Vienna"),
        ("Prague", "Reykjavik"),
        ("Vienna", "Split"),
    }
    # Build allowed ordered pairs for adjacency check
    allowed_pairs = set()
    for a, b in undirected_edges:
        allowed_pairs.add((idx[a], idx[b]))
        allowed_pairs.add((idx[b], idx[a]))

    days = 25
    s = Solver()

    # City variable per day: c[d] in 0..len(cities)-1
    c = [Int(f"c_{d}") for d in range(1, days + 1)]
    for d in range(days):
        s.add(And(c[d] >= 0, c[d] < len(cities)))

    # Helper: whether we're "in" city 'ci' on calendar day 'd' (1-based),
    # counting flight days for both departure and arrival cities.
    def in_city_on_day_expr(ci, d):
        # c[d-1] is the city assigned for day d
        # If there is a change on day d (d>=2 and c[d-1] != c[d-2]),
        # then day d counts for both c[d-1] (arrival) and c[d-2] (departure).
        current = c[d - 1] == ci
        if d >= 2:
            # departure credit from previous day (day d-1 city) if flight occurs on day d
            departure_credit = And(c[d - 2] == ci, c[d - 1] != c[d - 2])
            return Or(current, departure_credit)
        else:
            return current

    # Direct flight constraints between consecutive different-day cities
    for d in range(1, days):
        prev_city = c[d - 1]
        curr_city = c[d]
        s.add(Or(
            curr_city == prev_city,  # no flight that day
            Or([And(prev_city == i, curr_city == j) for (i, j) in allowed_pairs])
        ))

    # Attendance/event constraints:
    # Edinburgh show: days 5-8 inclusive
    for d in range(5, 9):
        s.add(in_city_on_day_expr(idx["Edinburgh"], d))

    # Split wedding: days 19-23 inclusive
    for d in range(19, 24):
        s.add(in_city_on_day_expr(idx["Split"], d))

    # City total presence-day constraints (including flight-day double counts)
    for name, req in required_days.items():
        ci = idx[name]
        total = Sum([If(in_city_on_day_expr(ci, d), 1, 0) for d in range(1, days + 1)])
        s.add(total == req)

    # Solve
    if s.check() != sat:
        raise RuntimeError("No valid itinerary found under given constraints.")

    m = s.model()
    itinerary = []
    for d in range(1, days + 1):
        city_name = cities[m.evaluate(c[d - 1]).as_long()]
        itinerary.append({"day": d, "city": city_name})

    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    solve_itinerary()
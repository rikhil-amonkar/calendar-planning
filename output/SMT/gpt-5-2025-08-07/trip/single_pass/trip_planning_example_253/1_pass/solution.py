# Requires: z3-solver (pip install z3-solver)
from z3 import Solver, Int, And, Or, If, Sum
import json

def solve_itinerary():
    # Cities and indices
    cities = ["Amsterdam", "Vienna", "Santorini", "Lyon"]
    idx = {name: i for i, name in enumerate(cities)}

    # Direct flight pairs (undirected)
    direct_pairs = {
        (idx["Vienna"], idx["Lyon"]),
        (idx["Lyon"], idx["Vienna"]),
        (idx["Vienna"], idx["Santorini"]),
        (idx["Santorini"], idx["Vienna"]),
        (idx["Vienna"], idx["Amsterdam"]),
        (idx["Amsterdam"], idx["Vienna"]),
        (idx["Amsterdam"], idx["Santorini"]),
        (idx["Santorini"], idx["Amsterdam"]),
        (idx["Lyon"], idx["Amsterdam"]),
        (idx["Amsterdam"], idx["Lyon"]),
    }

    days = 14
    s = Solver()

    # Variables: city per day (0..3)
    c = [Int(f"c_{d}") for d in range(1, days + 1)]
    for v in c:
        s.add(And(v >= 0, v < len(cities)))

    # Transitions must be either staying in the same city, or a direct flight
    for d in range(1, days):
        s.add(
            Or(
                c[d] == c[d - 1],
                Or(*[And(c[d - 1] == a, c[d] == b) for (a, b) in direct_pairs])
            )
        )

    # Count "presence" days with double-count rule:
    # Day d counts for city X if:
    # - c[d] == X (assigned city of the day), OR
    # - it's a flight day (c[d] != c[d-1]) and c[d-1] == X (previous city also counts)
    def presence_on_day(d, city_i):
        if d == 0:
            # Day index 0 corresponds to Day 1; no previous day
            return If(c[d] == city_i, 1, 0)
        return If(
            Or(
                c[d] == city_i,
                And(c[d] != c[d - 1], c[d - 1] == city_i),
            ),
            1,
            0,
        )

    # Desired total presence (including double-count)
    desired = {
        "Amsterdam": 3,
        "Vienna": 7,
        "Santorini": 4,
        "Lyon": 3,
    }

    # Enforce per-city presence totals
    for name, total in desired.items():
        i = idx[name]
        total_presence = Sum([presence_on_day(d, i) for d in range(days)])
        s.add(total_presence == total)

    # Number of flights = number of changes = 3 (since total presence sums to 17 = 14 + flights)
    flights = Sum([If(c[d] != c[d - 1], 1, 0) for d in range(1, days)])
    s.add(flights == 3)

    # Event constraints:
    # Workshop in Amsterdam between day 9 and day 11 (inclusive): must be "present" on at least one of these days
    ams = idx["Amsterdam"]
    s.add(
        Or(*[presence_on_day(d - 1, ams) == 1 for d in range(9, 12)])
    )

    # Wedding in Lyon between day 7 and day 9 (inclusive): must be "present" on at least one of these days
    lyon = idx["Lyon"]
    s.add(
        Or(*[presence_on_day(d - 1, lyon) == 1 for d in range(7, 10)])
    )

    if s.check().r == 1:  # sat
        m = s.model()
        itinerary = []
        for d in range(days):
            city_name = cities[m[c[d]].as_long()]
            itinerary.append({"day": d + 1, "place": city_name})
        print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))
    else:
        raise RuntimeError("No valid itinerary found")

if __name__ == "__main__":
    solve_itinerary()
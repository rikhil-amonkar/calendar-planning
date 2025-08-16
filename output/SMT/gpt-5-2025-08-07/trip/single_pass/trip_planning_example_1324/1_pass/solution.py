from z3 import Solver, Int, Bool, Sum, If, And, Or
import json

def solve_itinerary():
    days_total = 26

    cities = [
        "Venice",
        "Barcelona",
        "Copenhagen",
        "Lyon",
        "Reykjavik",
        "Dubrovnik",
        "Athens",
        "Tallinn",
        "Munich",
    ]
    idx = {name: i for i, name in enumerate(cities)}

    # Required total counted days per city (flight days count for both endpoints)
    required_days = {
        "Venice": 4,
        "Barcelona": 3,
        "Copenhagen": 4,
        "Lyon": 4,
        "Reykjavik": 4,
        "Dubrovnik": 5,
        "Athens": 2,
        "Tallinn": 5,
        "Munich": 3,
    }

    # Build directed adjacency (only direct flights allowed on change days)
    edges = set()

    def add_bidirectional(a, b):
        edges.add((idx[a], idx[b]))
        edges.add((idx[b], idx[a]))

    def add_direct(a, b):
        edges.add((idx[a], idx[b]))

    add_bidirectional("Copenhagen", "Athens")
    add_bidirectional("Copenhagen", "Dubrovnik")
    add_bidirectional("Munich", "Tallinn")
    add_bidirectional("Copenhagen", "Munich")
    add_bidirectional("Venice", "Munich")
    add_direct("Reykjavik", "Athens")  # one-way
    add_bidirectional("Athens", "Dubrovnik")
    add_bidirectional("Venice", "Athens")
    add_bidirectional("Lyon", "Barcelona")
    add_bidirectional("Copenhagen", "Reykjavik")
    add_bidirectional("Reykjavik", "Munich")
    add_bidirectional("Athens", "Munich")
    add_bidirectional("Lyon", "Munich")
    add_bidirectional("Barcelona", "Reykjavik")
    add_bidirectional("Venice", "Copenhagen")
    add_bidirectional("Barcelona", "Dubrovnik")
    add_bidirectional("Lyon", "Venice")
    add_bidirectional("Dubrovnik", "Munich")
    add_bidirectional("Barcelona", "Athens")
    add_bidirectional("Copenhagen", "Barcelona")
    add_bidirectional("Venice", "Barcelona")
    add_bidirectional("Barcelona", "Munich")
    add_bidirectional("Barcelona", "Tallinn")
    add_bidirectional("Copenhagen", "Tallinn")

    s = Solver()

    # Variables: city assigned for each day (1..26)
    City = [None] + [Int(f"city_{d}") for d in range(1, days_total + 1)]
    for d in range(1, days_total + 1):
        s.add(City[d] >= 0, City[d] < len(cities))

    # Changes (flights) between consecutive days d-1 -> d (so day d is the flight day if changed)
    change = [None, None] + [Bool(f"chg_{d}") for d in range(2, days_total + 1)]
    for d in range(2, days_total + 1):
        s.add(change[d] == (City[d] != City[d - 1]))
        # If change occurs, it must be a direct flight (directed edge prev->curr). If no change, allowed.
        s.add(
            Or(
                City[d] == City[d - 1],
                Or(*[And(City[d - 1] == i, City[d] == j) for (i, j) in edges]),
            )
        )

    # Exactly 8 changes (since 9 city blocks -> 8 transitions; aligns with double-counting to reach 34 total)
    s.add(Sum([If(change[d], 1, 0) for d in range(2, days_total + 1)]) == 8)

    # Helper: presence in city c on day d respecting the "flight day counts for both" rule.
    def is_in_city_day(c_idx, d):
        if d == 1:
            return City[d] == c_idx
        return Or(City[d] == c_idx, And(change[d], City[d - 1] == c_idx))

    # Counted days per city: day d counts if City[d]==c, and also day d counts for previous city if change on day d.
    for name, need in required_days.items():
        c_idx = idx[name]
        base_days = Sum([If(City[d] == c_idx, 1, 0) for d in range(1, days_total + 1)])
        extra_flight_days = Sum(
            [If(And(change[d], City[d - 1] == c_idx), 1, 0) for d in range(2, days_total + 1)]
        )
        s.add(base_days + extra_flight_days == need)

    # Window constraints (must be "in city" on at least one day in each window)
    # Barcelona meet friend between day 10 and 12
    s.add(
        Or(
            *[is_in_city_day(idx["Barcelona"], d) for d in range(10, 13)]
        )
    )
    # Copenhagen relatives between day 7 and 10
    s.add(
        Or(
            *[is_in_city_day(idx["Copenhagen"], d) for d in range(7, 11)]
        )
    )
    # Dubrovnik wedding between day 16 and 20
    s.add(
        Or(
            *[is_in_city_day(idx["Dubrovnik"], d) for d in range(16, 21)]
        )
    )

    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found under given constraints.")

    m = s.model()

    itinerary = []
    for d in range(1, days_total + 1):
        city_idx = m.evaluate(City[d]).as_long()
        itinerary.append({"day": d, "city": cities[city_idx]})

    print(json.dumps({"itinerary": itinerary}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    solve_itinerary()
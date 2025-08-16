# Solve the trip planning problem using Z3 and output a JSON itinerary.
# The key rule is: if you fly from city A to city B on day X, day X counts for BOTH A and B.
# We model one city per day (end-of-day location) and use the counting rule above.

from z3 import *
import json

def solve_itinerary():
    # Cities and indices
    cities = ["Mykonos", "Reykjavik", "Dublin", "London", "Helsinki", "Hamburg"]
    idx = {name: i for i, name in enumerate(cities)}
    n_days = 16

    # Direct flights (undirected)
    direct_pairs = [
        ("Dublin", "London"),
        ("Hamburg", "Dublin"),
        ("Helsinki", "Reykjavik"),
        ("Hamburg", "London"),
        ("Dublin", "Helsinki"),
        ("Reykjavik", "London"),
        ("London", "Mykonos"),
        ("Dublin", "Reykjavik"),
        ("Hamburg", "Helsinki"),
        ("Helsinki", "London"),
    ]

    # Build adjacency (including staying in the same city)
    neighbors = {i: set([i]) for i in range(len(cities))}
    for a, b in direct_pairs:
        ai, bi = idx[a], idx[b]
        neighbors[ai].add(bi)
        neighbors[bi].add(ai)

    # Z3 variables: city per day (end-of-day location)
    city = [Int(f"city_{d+1}") for d in range(n_days)]

    s = Solver()

    # Domain constraints
    for d in range(n_days):
        s.add(And(city[d] >= 0, city[d] < len(cities)))

    # Connectivity constraints: either stay or take a direct flight
    for d in range(1, n_days):
        ors = []
        for c_from in range(len(cities)):
            ors.append(And(city[d-1] == c_from, Or([city[d] == c_to for c_to in neighbors[c_from]])))
        s.add(Or(ors))

    # Helper: presence in a city on a given day according to the "both cities count on flight day" rule
    def present(c, day):  # day = 1..n_days
        if day == 1:
            return city[0] == c
        # Present if end-of-day city is c OR if the day is a departure day from c
        return Or(city[day-1] == c, And(city[day-2] == c, city[day-2] != city[day-1]))

    # Required total presence (days counted with the flight-day rule)
    required_days = {
        "Mykonos": 3,
        "Reykjavik": 2,
        "Dublin": 5,
        "London": 5,
        "Helsinki": 4,
        "Hamburg": 2,
    }

    # Sum of presence per city must match required_days
    for name, req in required_days.items():
        c = idx[name]
        s.add(Sum([If(present(c, d+1), 1, 0) for d in range(n_days)]) == req)

    # Specific day constraints:
    # - Meet friends in Hamburg between day 1 and day 2 (must be present in Hamburg on days 1 and 2)
    for d in [1, 2]:
        s.add(present(idx["Hamburg"], d))

    # - Annual show in Dublin from day 2 to day 6 (present each of those days)
    for d in range(2, 7):
        s.add(present(idx["Dublin"], d))

    # - Wedding in Reykjavik between day 9 and day 10 (present on days 9 and 10)
    for d in [9, 10]:
        s.add(present(idx["Reykjavik"], d))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    m = s.model()
    itinerary = [{"day": d+1, "city": cities[m[city[d]].as_long()]} for d in range(n_days)]
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_itinerary()
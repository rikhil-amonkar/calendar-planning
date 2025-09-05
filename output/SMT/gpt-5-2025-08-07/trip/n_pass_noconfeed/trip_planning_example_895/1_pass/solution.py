import json
from z3 import *

def main():
    # Define cities
    cities = ["Venice", "London", "Lisbon", "Brussels", "Reykjavik", "Santorini", "Madrid"]
    idx = {name: i for i, name in enumerate(cities)}
    n_days = 17  # Days 1..17, we use 0..16 as indices

    # Define allowed direct flights (directed)
    allowed_pairs = set()
    def add_bidirectional(a, b):
        allowed_pairs.add((idx[a], idx[b]))
        allowed_pairs.add((idx[b], idx[a]))
    def add_direct(a, b):
        allowed_pairs.add((idx[a], idx[b]))

    # Add edges based on the problem statement
    add_bidirectional("Venice", "Madrid")
    add_bidirectional("Lisbon", "Reykjavik")
    add_bidirectional("Brussels", "Venice")
    add_bidirectional("Venice", "Santorini")
    add_bidirectional("Lisbon", "Venice")
    add_direct("Reykjavik", "Madrid")  # directional
    add_bidirectional("Brussels", "London")
    add_bidirectional("Madrid", "London")
    add_bidirectional("Santorini", "London")
    add_bidirectional("London", "Reykjavik")
    add_bidirectional("Brussels", "Lisbon")
    add_bidirectional("Lisbon", "London")
    add_bidirectional("Lisbon", "Madrid")
    add_bidirectional("Madrid", "Santorini")
    add_bidirectional("Brussels", "Reykjavik")
    add_bidirectional("Brussels", "Madrid")
    add_bidirectional("Venice", "London")

    # SMT variables: city per day (0..6)
    c = [Int(f"city_{d}") for d in range(n_days)]

    s = Solver()

    # Domain constraint
    for d in range(n_days):
        s.add(And(c[d] >= 0, c[d] < len(cities)))

    # Helper: presence predicate according to travel rule
    def present_expr(k, d):
        if d == 0:
            return c[0] == k
        else:
            return Or(c[d] == k, And(c[d-1] == k, c[d] != c[d-1]))

    # Exactly-one-flight-per-day model: move is c[d] != c[d-1] (implicit by variables)
    # Enforce direct connection when moving
    for d in range(1, n_days):
        # Either stay or have an allowed directed edge
        allowed_or = Or([And(c[d-1] == i, c[d] == j) for (i, j) in allowed_pairs])
        s.add(Or(c[d] == c[d-1], allowed_or))

    # Duration requirements
    required_days = {
        "Venice": 3,
        "London": 3,
        "Lisbon": 4,
        "Brussels": 2,
        "Reykjavik": 3,
        "Santorini": 3,
        "Madrid": 5
    }

    for name, req in required_days.items():
        k = idx[name]
        total = Sum([If(present_expr(k, d), 1, 0) for d in range(n_days)])
        s.add(total == req)

    # Hard time-window constraints:
    # Conference in Brussels on day 1 and day 2 -> presence on days 1 and 2 (indices 0,1)
    s.add(present_expr(idx["Brussels"], 0))
    s.add(present_expr(idx["Brussels"], 1))

    # Relatives in Venice between day 5 and day 7 inclusive (indices 4,5,6)
    s.add(present_expr(idx["Venice"], 4))
    s.add(present_expr(idx["Venice"], 5))
    s.add(present_expr(idx["Venice"], 6))

    # Wedding in Madrid between day 7 and day 11 inclusive (indices 6..10)
    for d in range(6, 11):
        s.add(present_expr(idx["Madrid"], d))

    # Ensure we actually use the specified set of seven European cities (implicitly ensured by durations)
    # Also ensure start day (day 1) is Brussels to satisfy day 1 presence without prior-day ambiguity
    s.add(c[0] == idx["Brussels"])

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": [], "status": "unsat"}))
        return

    m = s.model()
    plan = [m.evaluate(c[d]).as_long() for d in range(n_days)]
    # Build contiguous main-city ranges (based on staying city c[d])
    itinerary = []
    start = 0
    current = plan[0]
    for d in range(1, n_days):
        if plan[d] != current:
            # Close previous segment Day start+1 to d
            itinerary.append({
                "day_range": f"Day {start+1}-{d}",
                "place": cities[current]
            })
            start = d
            current = plan[d]
    # Close last segment
    itinerary.append({
        "day_range": f"Day {start+1}-{n_days}",
        "place": cities[current]
    })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
import json
from z3 import *

def main():
    # Define cities and mapping
    cities = [
        "Vienna",      # 0
        "Barcelona",   # 1
        "Edinburgh",   # 2
        "Krakow",      # 3
        "Riga",        # 4
        "Hamburg",     # 5
        "Paris",       # 6
        "Stockholm"    # 7
    ]
    VIENNA, BARCELONA, EDINBURGH, KRAKOW, RIGA, HAMBURG, PARIS, STOCKHOLM = range(8)

    # Duration requirements per city
    required_days = {
        VIENNA: 4,
        BARCELONA: 2,
        EDINBURGH: 4,
        KRAKOW: 3,
        RIGA: 4,
        HAMBURG: 2,
        PARIS: 2,
        STOCKHOLM: 2
    }

    # Allowed direct flights (directed edges)
    edges = set()

    def add_bidirectional(a, b):
        edges.add((a, b))
        edges.add((b, a))

    # Add edges as per the provided list
    add_bidirectional(HAMBURG, STOCKHOLM)
    add_bidirectional(VIENNA, STOCKHOLM)
    add_bidirectional(PARIS, EDINBURGH)
    add_bidirectional(RIGA, BARCELONA)
    add_bidirectional(PARIS, RIGA)
    add_bidirectional(KRAKOW, BARCELONA)
    add_bidirectional(EDINBURGH, STOCKHOLM)
    add_bidirectional(PARIS, KRAKOW)
    add_bidirectional(KRAKOW, STOCKHOLM)
    add_bidirectional(RIGA, EDINBURGH)
    add_bidirectional(BARCELONA, STOCKHOLM)
    add_bidirectional(PARIS, STOCKHOLM)
    add_bidirectional(KRAKOW, EDINBURGH)
    add_bidirectional(VIENNA, HAMBURG)
    add_bidirectional(PARIS, HAMBURG)
    add_bidirectional(RIGA, STOCKHOLM)
    add_bidirectional(HAMBURG, BARCELONA)
    add_bidirectional(VIENNA, BARCELONA)
    add_bidirectional(KRAKOW, VIENNA)
    # Directed edge: from Riga to Hamburg
    edges.add((RIGA, HAMBURG))
    add_bidirectional(BARCELONA, EDINBURGH)
    add_bidirectional(PARIS, BARCELONA)
    add_bidirectional(HAMBURG, EDINBURGH)
    add_bidirectional(PARIS, VIENNA)
    add_bidirectional(VIENNA, RIGA)

    days = list(range(1, 17))  # 1..16 inclusive

    # Z3 variables: City on day t is an Int in [0..7]
    City = [None] + [Int(f"City_{t}") for t in days]  # index 0 unused

    s = Solver()

    # Domain constraints
    for t in days:
        s.add(And(City[t] >= 0, City[t] < len(cities)))

    # Count changes (flights) between consecutive days; need exactly 7
    change_bools = []
    for t in range(2, 17):
        change_bools.append(City[t] != City[t-1])
    num_changes = Sum([If(cb, 1, 0) for cb in change_bools])
    s.add(num_changes == 7)

    # Direct flight constraint: if City changes on day t, must be an allowed direct flight from day t-1 city to day t city
    for t in range(2, 17):
        allowed_pairs = [And(City[t-1] == i, City[t] == j) for (i, j) in edges]
        s.add(Implies(City[t] != City[t-1], Or(*allowed_pairs)))

    # Helper: presence of city c on day t
    def present(c, t):
        if t == 1:
            return City[t] == c
        else:
            # Present if end-of-day city is c, or if you depart from c on day t (i.e., change from c at t)
            return Or(City[t] == c, And(City[t-1] == c, City[t] != City[t-1]))

    # Duration constraints: exact day counts per city, counting flight days as presence in both cities
    for c in range(8):
        base = Sum([If(City[t] == c, 1, 0) for t in days])
        extra = Sum([If(And(City[t-1] == c, City[t] != City[t-1]), 1, 0) for t in range(2, 17)])
        s.add(base + extra == required_days[c])

    # Time window constraints
    # - Wedding in Paris between day 1 and day 2 (present on at least one of these days)
    s.add(Or(present(PARIS, 1), present(PARIS, 2)))

    # - Conference in Hamburg during day 10 and day 11 (present both days)
    s.add(present(HAMBURG, 10))
    s.add(present(HAMBURG, 11))

    # - Meet friend in Edinburgh between day 12 and day 15 (present at least one of these days)
    s.add(Or(*[present(EDINBURGH, t) for t in range(12, 16)]))

    # - Visit relatives in Stockholm between day 15 and day 16 (present at least one of these days)
    s.add(Or(present(STOCKHOLM, 15), present(STOCKHOLM, 16)))

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    m = s.model()

    # Extract day-by-day end-of-day city assignments
    day_cities = [None] + [m.evaluate(City[t]).as_long() for t in days]

    # Build contiguous segments by end-of-day city
    itinerary = []
    start_day = 1
    current_city = day_cities[1]
    for t in range(2, 17):
        if day_cities[t] != current_city:
            itinerary.append({
                "day_range": f"Day {start_day}-{t-1}",
                "place": cities[current_city]
            })
            start_day = t
            current_city = day_cities[t]
    # Append last segment
    itinerary.append({
        "day_range": f"Day {start_day}-16",
        "place": cities[current_city]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
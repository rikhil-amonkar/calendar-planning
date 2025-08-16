import json
from z3 import *

def solve_itinerary():
    # Days are 1..23
    num_days = 23

    # City indices
    cities = [
        "Riga",        # 0
        "Manchester",  # 1
        "Bucharest",   # 2
        "Florence",    # 3
        "Vienna",      # 4
        "Istanbul",    # 5
        "Reykjavik",   # 6
        "Stuttgart"    # 7
    ]
    city_index = {name: i for i, name in enumerate(cities)}

    # Required total counted days per city
    required_days = {
        "Riga": 4,
        "Manchester": 5,
        "Bucharest": 4,
        "Florence": 4,
        "Vienna": 2,
        "Istanbul": 2,
        "Reykjavik": 4,
        "Stuttgart": 5
    }

    # Allowed directed edges (direct flights). "A and B" => both directions allowed.
    edges = set()
    def add_bidirectional(a, b):
        edges.add((city_index[a], city_index[b]))
        edges.add((city_index[b], city_index[a]))
    def add_unidirectional(a, b):
        edges.add((city_index[a], city_index[b]))

    add_bidirectional("Bucharest", "Vienna")
    add_bidirectional("Reykjavik", "Vienna")
    add_bidirectional("Manchester", "Vienna")
    add_bidirectional("Manchester", "Riga")
    add_bidirectional("Riga", "Vienna")
    add_bidirectional("Istanbul", "Vienna")
    add_bidirectional("Vienna", "Florence")
    add_bidirectional("Stuttgart", "Vienna")
    add_bidirectional("Riga", "Bucharest")
    add_bidirectional("Istanbul", "Riga")
    add_bidirectional("Stuttgart", "Istanbul")
    add_unidirectional("Reykjavik", "Stuttgart")  # one-way
    add_bidirectional("Istanbul", "Bucharest")
    add_bidirectional("Manchester", "Istanbul")
    add_bidirectional("Manchester", "Bucharest")
    add_bidirectional("Stuttgart", "Manchester")

    s = Solver()

    # city[d] is the city index at the end of day d (0-based index for days)
    city = [Int(f"city_{d}") for d in range(num_days)]
    for d in range(num_days):
        s.add(And(city[d] >= 0, city[d] < len(cities)))

    # Occurrence booleans: occur[c][d] => city c is counted on day d (1-based semantics)
    occur = [[Bool(f"occur_{c}_{d}") for d in range(num_days)] for c in range(len(cities))]

    for c in range(len(cities)):
        # Day 1 (index 0): counted iff city[0] == c
        s.add(occur[c][0] == (city[0] == c))
        # Days 2..23: counted if end-of-day city is c OR if we departed from c that day
        for d in range(1, num_days):
            s.add(
                occur[c][d] ==
                Or(
                    city[d] == c,                          # Being in c at end of day d
                    And(city[d - 1] == c, city[d] != city[d - 1])  # Departed c on day d
                )
            )

    # Flight (adjacency) constraints: if city changes between d-1 and d, must be a direct edge
    for d in range(1, num_days):
        allowed_moves = [And(city[d - 1] == i, city[d] == j) for (i, j) in edges]
        s.add(Or(city[d] == city[d - 1], Or(*allowed_moves)))

    # Per-city total counted days constraints
    for name, req in required_days.items():
        cidx = city_index[name]
        total = Sum([If(occur[cidx][d], 1, 0) for d in range(num_days)])
        s.add(total == req)

    # Events:
    # Istanbul on days 12 and 13
    day12_idx = 12 - 1
    day13_idx = 13 - 1
    s.add(occur[city_index["Istanbul"]][day12_idx])
    s.add(occur[city_index["Istanbul"]][day13_idx])

    # Bucharest on days 16, 17, 18, 19
    for d in [16, 17, 18, 19]:
        s.add(occur[city_index["Bucharest"]][d - 1])

    # Optional: enforce that total number of flights (transitions) equals sum(required)-num_days = 30-23 = 7
    transitions = Sum([If(city[d] != city[d - 1], 1, 0) for d in range(1, num_days)])
    s.add(transitions == (sum(required_days.values()) - num_days))  # 7

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()
    itinerary = []
    for d in range(num_days):
        cidx = m[city[d]].as_long()
        itinerary.append({"day": d + 1, "place": cities[cidx]})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False, indent=2))
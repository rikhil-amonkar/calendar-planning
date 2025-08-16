import json
from z3 import *

def solve_itinerary():
    # Cities and required stays (counts include double-counted flight days)
    cities = ["Amsterdam", "Edinburgh", "Brussels", "Vienna", "Berlin", "Reykjavik"]
    idx = {name: i for i, name in enumerate(cities)}
    required_days = {
        "Amsterdam": 4,
        "Edinburgh": 5,
        "Brussels": 5,
        "Vienna": 5,
        "Berlin": 4,
        "Reykjavik": 5,
    }

    total_days = 23

    # Direct flight edges (undirected)
    edges = {
        ("Edinburgh", "Berlin"),
        ("Amsterdam", "Berlin"),
        ("Edinburgh", "Amsterdam"),
        ("Vienna", "Berlin"),
        ("Berlin", "Brussels"),
        ("Vienna", "Reykjavik"),
        ("Edinburgh", "Brussels"),
        ("Vienna", "Brussels"),
        ("Amsterdam", "Reykjavik"),
        ("Reykjavik", "Brussels"),
        ("Amsterdam", "Vienna"),
        ("Reykjavik", "Berlin"),
    }

    edge_set = set()
    for a, b in edges:
        edge_set.add((idx[a], idx[b]))
        edge_set.add((idx[b], idx[a]))

    s = Optimize()

    # Day -> City assignment (1-based days)
    day_city = [None] + [Int(f"day_{d}") for d in range(1, total_days + 1)]
    for d in range(1, total_days + 1):
        s.add(And(day_city[d] >= 0, day_city[d] < len(cities)))

    # Only direct flights between consecutive days (or stay in the same city)
    for d in range(2, total_days + 1):
        s.add(Or(day_city[d] == day_city[d - 1],
                 Or([And(day_city[d - 1] == a, day_city[d] == b) for (a, b) in edge_set])))

    # presence[c][d] = you are present in city c on day d
    # present if:
    # - day_city[d] == c (assigned)
    # - OR (d>1 and day_city[d-1] == c and day_city[d] != day_city[d-1]) (you flew away on day d)
    present = {
        c: [None] + [Bool(f"present_{cities[c]}_{d}") for d in range(1, total_days + 1)]
        for c in range(len(cities))
    }

    for c in range(len(cities)):
        for d in range(1, total_days + 1):
            if d == 1:
                s.add(present[c][d] == (day_city[d] == c))
            else:
                s.add(present[c][d] == Or(day_city[d] == c,
                                          And(day_city[d - 1] == c, day_city[d] != day_city[d - 1])))

    # Required total presence days per city
    for name, req in required_days.items():
        c = idx[name]
        s.add(Sum([If(present[c][d], 1, 0) for d in range(1, total_days + 1)]) == req)

    # Windows:
    # - Amsterdam between day 5 and day 8 (inclusive)
    s.add(Or([present[idx["Amsterdam"]][d] for d in range(5, 9)]))
    # - Berlin between day 16 and day 19 (inclusive)
    s.add(Or([present[idx["Berlin"]][d] for d in range(16, 20)]))
    # - Reykjavik between day 12 and day 16 (inclusive)
    s.add(Or([present[idx["Reykjavik"]][d] for d in range(12, 17)]))

    # (Optional but consistent) The number of flights equals 5 because sum(required_days)=28 and total_days=23
    # sum of presences = total_days + flights = 28 => flights = 5
    flights = [If(day_city[d] != day_city[d - 1], 1, 0) for d in range(2, total_days + 1)]
    s.add(Sum(flights) == 5)

    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found.")

    m = s.model()
    itinerary = []
    for d in range(1, total_days + 1):
        c = m.evaluate(day_city[d]).as_long()
        itinerary.append({"day": d, "city": cities[c]})

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    solve_itinerary()
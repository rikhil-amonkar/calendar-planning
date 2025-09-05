import json
from z3 import *

def main():
    # Define cities and their required durations
    cities = ["Vienna", "Lyon", "Edinburgh", "Reykjavik", "Stuttgart", "Manchester", "Split", "Prague"]
    city_to_id = {name: i for i, name in enumerate(cities)}
    durations = {
        city_to_id["Vienna"]: 4,
        city_to_id["Lyon"]: 3,
        city_to_id["Edinburgh"]: 4,
        city_to_id["Reykjavik"]: 5,
        city_to_id["Stuttgart"]: 5,
        city_to_id["Manchester"]: 2,
        city_to_id["Split"]: 5,
        city_to_id["Prague"]: 4,
    }

    # Direct flight edges (treated as undirected)
    edge_pairs = [
        ("Reykjavik","Stuttgart"),
        ("Stuttgart","Split"),
        ("Stuttgart","Vienna"),
        ("Prague","Manchester"),
        ("Edinburgh","Prague"),
        ("Manchester","Split"),
        ("Prague","Vienna"),
        ("Vienna","Manchester"),
        ("Prague","Split"),
        ("Vienna","Lyon"),
        ("Stuttgart","Edinburgh"),
        ("Split","Lyon"),
        ("Stuttgart","Manchester"),
        ("Prague","Lyon"),
        ("Reykjavik","Vienna"),
        ("Prague","Reykjavik"),
        ("Vienna","Split"),
    ]
    edges = set()
    for a, b in edge_pairs:
        ai, bi = city_to_id[a], city_to_id[b]
        edges.add((ai, bi))
        edges.add((bi, ai))

    n = len(cities)  # 8
    total_days = 25

    # Z3 variables
    order = [Int(f"order_{i}") for i in range(n)]  # permutation of city IDs
    start = [Int(f"start_{i}") for i in range(n)]  # inclusive start day
    end_ = [Int(f"end_{i}") for i in range(n)]     # inclusive end day

    s = Solver()

    # Each position is a city ID within range and all distinct -> permutation of all cities
    for i in range(n):
        s.add(And(order[i] >= 0, order[i] < n))
    s.add(Distinct(order))

    # Start at day 1 and chain segments with one-day overlaps (travel day counts for both)
    s.add(start[0] == 1)
    for i in range(n):
        # duration of the city at position i
        dur_i = Sum([If(order[i] == cid, durations[cid], 0) for cid in range(n)])
        s.add(end_[i] == start[i] + dur_i - 1)
        if i < n - 1:
            # Next segment starts on the same day this one ends (overlap on travel day)
            s.add(start[i + 1] == end_[i])

    # Total unique days covered end with day 25
    s.add(end_[n - 1] == total_days)

    # Enforce direct flight between consecutive cities
    for i in range(n - 1):
        s.add(Or([And(order[i] == a, order[i + 1] == b) for (a, b) in edges]))

    # Fixed-date events:
    # Edinburgh days 5-8
    edinburgh_id = city_to_id["Edinburgh"]
    s.add(Or([And(order[i] == edinburgh_id, start[i] == 5) for i in range(n)]))

    # Split days 19-23
    split_id = city_to_id["Split"]
    s.add(Or([And(order[i] == split_id, start[i] == 19) for i in range(n)]))

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": [], "status": "unsat"}))
        return

    m = s.model()

    # Extract itinerary
    itinerary = []
    for i in range(n):
        cid = m.evaluate(order[i]).as_long()
        st = m.evaluate(start[i]).as_long()
        en = m.evaluate(end_[i]).as_long()
        itinerary.append({
            "day_range": f"Day {st}-{en}",
            "place": cities[cid]
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
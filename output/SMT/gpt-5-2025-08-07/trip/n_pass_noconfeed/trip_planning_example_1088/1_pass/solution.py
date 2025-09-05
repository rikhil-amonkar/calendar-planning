import json
from z3 import *

def main():
    # Define cities and indices
    cities = ["Reykjavik", "Stuttgart", "Oslo", "Split", "Geneva", "Porto", "Tallinn", "Stockholm"]
    idx = {name: i for i, name in enumerate(cities)}
    n_cities = len(cities)
    days = list(range(1, 22))  # Day 1..21

    # Direct flight edges (undirected)
    undirected_edges = [
        ("Reykjavik", "Stuttgart"),
        ("Reykjavik", "Stockholm"),
        ("Reykjavik", "Tallinn"),
        ("Stockholm", "Oslo"),
        ("Stuttgart", "Porto"),
        ("Oslo", "Split"),
        ("Stockholm", "Stuttgart"),
        ("Reykjavik", "Oslo"),
        ("Oslo", "Geneva"),
        ("Stockholm", "Split"),
        ("Split", "Stuttgart"),
        ("Tallinn", "Oslo"),
        ("Stockholm", "Geneva"),
        ("Oslo", "Porto"),
        ("Geneva", "Porto"),
        ("Geneva", "Split"),
    ]
    edges = set()
    for a, b in undirected_edges:
        i, j = idx[a], idx[b]
        edges.add((i, j))
        edges.add((j, i))

    # Desired durations (soft targets)
    desired_durations = {
        "Oslo": 5,
        "Stuttgart": 5,
        "Reykjavik": 2,
        "Split": 3,
        "Geneva": 2,
        "Porto": 3,
        "Tallinn": 5,
        "Stockholm": 3,
    }
    targets = [desired_durations[c] for c in cities]

    # SMT variables
    City = {t: Int(f"City_{t}") for t in days}
    Present = {(t, c): Bool(f"Present_{t}_{c}") for t in days for c in range(n_cities)}

    opt = Optimize()

    # Domain constraints for City[t]
    for t in days:
        opt.add(And(City[t] >= 0, City[t] < n_cities))

    # Movement and presence constraints
    # Day 1 presence equivalence
    for c in range(n_cities):
        opt.add(Present[(1, c)] == (City[1] == c))

    # For t >= 2: direct flights constraint and presence definition
    for t in range(2, 22):
        # If city changes, it must be along a direct edge
        change_cases = [And(City[t - 1] == i, City[t] == j) for (i, j) in edges]
        opt.add(Or(City[t] == City[t - 1], Or(change_cases)))

        for c in range(n_cities):
            # Present at day t if in City[t] == c, or if you departed from c on day t (i.e., City[t-1]==c and changed)
            opt.add(Present[(t, c)] == Or(City[t] == c, And(City[t - 1] == c, City[t] != City[t - 1])))

    # Hard constraints:
    # - Attend conference in Reykjavik on day 1 and day 2
    opt.add(Present[(1, idx["Reykjavik"])])
    opt.add(Present[(2, idx["Reykjavik"])])

    # - Attend workshop in Porto between day 19 and day 21 (inclusive)
    for d in [19, 20, 21]:
        opt.add(Present[(d, idx["Porto"])])
    # - Meet friend in Stockholm between day 2 and day 4 (at least one of those days)
    opt.add(Or(Present[(2, idx["Stockholm"])], Present[(3, idx["Stockholm"])], Present[(4, idx["Stockholm"])]))

    # - Visit all 8 cities (at least one day presence in each)
    for c in range(n_cities):
        opt.add(Sum([If(Present[(t, c)], 1, 0) for t in days]) >= 1)

    # Durations per city
    durations = []
    diffs = []
    for c in range(n_cities):
        dur_c = Int(f"dur_{c}")
        opt.add(dur_c == Sum([If(Present[(t, c)], 1, 0) for t in days]))
        durations.append(dur_c)

        diff_c = Int(f"diff_{c}")
        tgt = targets[c]
        opt.add(diff_c >= dur_c - tgt)
        opt.add(diff_c >= tgt - dur_c)
        opt.add(diff_c >= 0)
        diffs.append(diff_c)

    # Objective 1: minimize total absolute deviation from desired durations
    total_abs_deviation = Int("total_abs_deviation")
    opt.add(total_abs_deviation == Sum(diffs))
    opt.minimize(total_abs_deviation)

    # Objective 2: minimize number of flights (city changes)
    flights = [If(City[t] != City[t - 1], 1, 0) for t in range(2, 22)]
    total_flights = Int("total_flights")
    opt.add(total_flights == Sum(flights))
    opt.minimize(total_flights)

    # Solve
    if opt.check() != sat:
        print(json.dumps({"itinerary": [], "status": "UNSAT"}))
        return

    model = opt.model()

    # Extract city per day
    city_per_day = [None] * (len(days) + 1)  # 1-indexed
    for t in days:
        city_idx = model.evaluate(City[t]).as_long()
        city_per_day[t] = cities[city_idx]

    # Build compressed day ranges by base city (City[t])
    itinerary = []
    start = 1
    current_city = city_per_day[1]
    for t in range(2, 22):
        if city_per_day[t] != current_city:
            itinerary.append({"day_range": f"Day {start}-{t-1}", "place": current_city})
            start = t
            current_city = city_per_day[t]
    itinerary.append({"day_range": f"Day {start}-21", "place": current_city})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
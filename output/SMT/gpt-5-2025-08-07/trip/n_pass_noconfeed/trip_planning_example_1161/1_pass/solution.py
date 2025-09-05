import json
from z3 import *

def main():
    # Define cities
    cities = [
        "Oslo",
        "Krakow",
        "Paris",
        "Madrid",
        "Helsinki",
        "Vilnius",
        "Dubrovnik",
        "Mykonos",
    ]
    city_to_idx = {name: i for i, name in enumerate(cities)}
    idx_to_city = {i: name for name, i in city_to_idx.items()}
    n_cities = len(cities)

    # Flight graph (directed). "A and B" means both directions.
    edges = set()
    def add_bidirectional(a, b):
        edges.add((city_to_idx[a], city_to_idx[b]))
        edges.add((city_to_idx[b], city_to_idx[a]))
    def add_directed(a, b):
        edges.add((city_to_idx[a], city_to_idx[b]))

    add_bidirectional("Oslo", "Krakow")
    add_bidirectional("Oslo", "Paris")
    add_bidirectional("Paris", "Madrid")
    add_bidirectional("Helsinki", "Vilnius")
    add_bidirectional("Oslo", "Madrid")
    add_bidirectional("Oslo", "Helsinki")
    add_bidirectional("Helsinki", "Krakow")
    add_bidirectional("Dubrovnik", "Helsinki")
    add_bidirectional("Dubrovnik", "Madrid")
    add_bidirectional("Oslo", "Dubrovnik")
    add_bidirectional("Krakow", "Paris")
    add_bidirectional("Madrid", "Mykonos")
    add_bidirectional("Oslo", "Vilnius")
    add_directed("Krakow", "Vilnius")  # one-way
    add_bidirectional("Helsinki", "Paris")
    add_bidirectional("Vilnius", "Paris")
    add_bidirectional("Helsinki", "Madrid")

    total_days = 18

    # Requirements
    req_exact_hard = {
        "Oslo": 2,
        "Dubrovnik": 3,
        "Mykonos": 4,
    }
    # Desired durations (soft/optimization-driven)
    req_soft = {
        "Krakow": 5,
        "Vilnius": 2,
        "Helsinki": 2,
        "Madrid": 5,
        "Paris": 2,
    }

    # Day-window presence constraints (hard)
    # Dubrovnik show day 2-4
    must_be_in_dub_days = [2, 3, 4]
    # Meet friends in Oslo day 1-2
    must_be_in_oslo_days = [1, 2]
    # Visit relatives in Mykonos days 15-18
    must_be_in_mykonos_days = [15, 16, 17, 18]

    Oslo = city_to_idx["Oslo"]
    Krakow = city_to_idx["Krakow"]
    Paris = city_to_idx["Paris"]
    Madrid = city_to_idx["Madrid"]
    Helsinki = city_to_idx["Helsinki"]
    Vilnius = city_to_idx["Vilnius"]
    Dubrovnik = city_to_idx["Dubrovnik"]
    Mykonos = city_to_idx["Mykonos"]

    # SMT model
    opt = Optimize()
    opt.set(priority='lex')

    # Base city per day (start-of-day city; at most one flight per day to next)
    c = [Int(f"c_{d}") for d in range(1, total_days + 1)]
    for d in range(total_days):
        opt.add(And(c[d] >= 0, c[d] < n_cities))

    # Direct flight or stay constraint between consecutive days
    allowed_pairs = list(edges)
    for d in range(total_days - 1):
        # Either stay in same city or take a direct flight
        pair_constraints = [And(c[d] == i, c[d + 1] == j) for (i, j) in allowed_pairs]
        opt.add(Or(c[d + 1] == c[d], Or(pair_constraints)))

    # counted[city][day] is True iff on day d the traveler is considered in 'city':
    # Either the base city that day is 'city' OR a flight is taken that day into 'city' (i.e., next day's base).
    counted = {
        ci: [Bool(f"counted_{ci}_{d}") for d in range(1, total_days + 1)]
        for ci in range(n_cities)
    }
    for ci in range(n_cities):
        for d in range(total_days):
            # If d < total_days - 1, you can arrive into city on day d (c[d+1] == ci)
            if d < total_days - 1:
                opt.add(counted[ci][d] == Or(c[d] == ci, c[d + 1] == ci))
            else:
                # On last day, no "arrival to next day", so only base city counts
                opt.add(counted[ci][d] == (c[d] == ci))

    # Count days per city (with flight-day double counting)
    counted_days = {}
    for ci in range(n_cities):
        counted_days[ci] = Sum([If(counted[ci][d], 1, 0) for d in range(total_days)])

    # Attendance windows (hard)
    # Dubrovnik on days 2..4
    for d in must_be_in_dub_days:
        opt.add(counted[Dubrovnik][d - 1])
    # Oslo on days 1..2
    for d in must_be_in_oslo_days:
        opt.add(counted[Oslo][d - 1])
    # Mykonos on days 15..18
    for d in must_be_in_mykonos_days:
        opt.add(counted[Mykonos][d - 1])

    # Exact hard duration requirements
    for name, val in req_exact_hard.items():
        ci = city_to_idx[name]
        opt.add(counted_days[ci] == val)

    # Must visit all 8 cities at least once (counted)
    for ci in range(n_cities):
        opt.add(counted_days[ci] >= 1)

    # Optimization: minimize deviation from desired soft durations
    dev_vars = []
    for name, target in req_soft.items():
        ci = city_to_idx[name]
        dev = Int(f"dev_{ci}")
        opt.add(dev >= 0)
        opt.add(dev >= counted_days[ci] - target)
        opt.add(dev >= target - counted_days[ci])
        dev_vars.append(dev)

    total_deviation = Sum(dev_vars)
    opt.minimize(total_deviation)

    # Secondary objective: minimize number of flight days (changes)
    changes = [Bool(f"change_{d}") for d in range(1, total_days)]
    for d in range(total_days - 1):
        opt.add(changes[d] == (c[d] != c[d + 1]))
    total_changes = Sum([If(ch, 1, 0) for ch in changes])
    opt.minimize(total_changes)

    # Solve
    if opt.check() != sat:
        # If somehow unsat, return an empty itinerary
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()
    base_cities = [model.evaluate(c[d]).as_long() for d in range(total_days)]

    # Build contiguous day ranges for the base city itinerary
    itinerary = []
    start = 1
    current_city = base_cities[0]
    for day in range(2, total_days + 1):
        if base_cities[day - 1] != current_city:
            itinerary.append({
                "day_range": f"Day {start}-{day - 1}",
                "place": idx_to_city[current_city]
            })
            start = day
            current_city = base_cities[day - 1]
    # Append last segment
    itinerary.append({
        "day_range": f"Day {start}-{total_days}",
        "place": idx_to_city[current_city]
    })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
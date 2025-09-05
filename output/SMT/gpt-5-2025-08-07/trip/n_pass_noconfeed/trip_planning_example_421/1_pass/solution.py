import json
from z3 import *

def main():
    # Parameters
    n_days = 20
    cities = ["Nice", "Dublin", "Krakow", "Lyon", "Frankfurt"]
    idx = {name: i for i, name in enumerate(cities)}
    # Desired total credited days per city (counts flight days for both origin and destination)
    desired_days = {
        "Nice": 5,
        "Krakow": 6,
        "Dublin": 7,
        "Lyon": 4,
        "Frankfurt": 2,
    }

    # Direct flights (undirected)
    direct_edges = {
        ("Nice", "Dublin"),
        ("Dublin", "Frankfurt"),
        ("Dublin", "Krakow"),
        ("Krakow", "Frankfurt"),
        ("Lyon", "Frankfurt"),
        ("Nice", "Frankfurt"),
        ("Lyon", "Dublin"),
        ("Nice", "Lyon"),
    }
    # Build symmetric adjacency as allowed index pairs
    allowed_pairs = set()
    for a, b in direct_edges:
        allowed_pairs.add((idx[a], idx[b]))
        allowed_pairs.add((idx[b], idx[a]))

    # Z3 variables
    City = [None] + [Int(f"city_{d}") for d in range(1, n_days + 1)]  # 1..n_days
    Change = [None] + [Bool(f"change_{d}") for d in range(1, n_days + 1)]
    Credited = {}  # (d, c) -> Bool
    for d in range(1, n_days + 1):
        for c in range(len(cities)):
            Credited[(d, c)] = Bool(f"cred_{d}_{c}")

    opt = Optimize()

    # Domain constraints
    for d in range(1, n_days + 1):
        opt.add(And(City[d] >= 0, City[d] < len(cities)))

    # Change definitions
    opt.add(Change[1] == False)
    for d in range(2, n_days + 1):
        opt.add(Change[d] == (City[d] != City[d - 1]))

    # Direct flight constraints: if a change occurs on day d, the pair (City[d-1], City[d]) must be an allowed pair
    for d in range(2, n_days + 1):
        pair_allowed = Or([And(City[d - 1] == a, City[d] == b) for (a, b) in allowed_pairs]) if allowed_pairs else False
        opt.add(Implies(Change[d], pair_allowed))

    # Credited-day definition:
    # On day d, you are credited for the city you are in after flying that day (City[d]),
    # and if a flight occurred on day d, you are also credited for the origin city City[d-1].
    for d in range(1, n_days + 1):
        for c in range(len(cities)):
            if d == 1:
                opt.add(Credited[(d, c)] == (City[d] == c))
            else:
                opt.add(Credited[(d, c)] == Or(City[d] == c, And(Change[d], City[d - 1] == c)))

    # Duration constraints per city
    for name, days_needed in desired_days.items():
        c = idx[name]
        opt.add(Sum([If(Credited[(d, c)], 1, 0) for d in range(1, n_days + 1)]) == days_needed)

    # Nice must be credited on each of days 1..5 (inclusive), and on no other day
    c_nice = idx["Nice"]
    for d in range(1, 6):
        opt.add(Credited[(d, c_nice)] == True)
    for d in range(6, n_days + 1):
        opt.add(Credited[(d, c_nice)] == False)

    # Meet friends in Frankfurt between day 19 and 20: enforce being in Frankfurt both days
    c_fr = idx["Frankfurt"]
    opt.add(City[19] == c_fr)
    opt.add(City[20] == c_fr)

    # Minimize number of flight days (changes)
    total_changes = Sum([If(Change[d], 1, 0) for d in range(2, n_days + 1)])
    opt.minimize(total_changes)

    # Solve
    if opt.check() != sat:
        print(json.dumps({"itinerary": [], "status": "unsat"}))
        return

    m = opt.model()

    # Build non-overlapping itinerary by base city per day (City[d] after any flight that day)
    day_cities = [None] + [cities[m.evaluate(City[d]).as_long()] for d in range(1, n_days + 1)]

    itinerary = []
    start = 1
    current = day_cities[1]
    for d in range(2, n_days + 1):
        if day_cities[d] != current:
            itinerary.append({"day_range": f"Day {start}-{d-1}", "place": current})
            start = d
            current = day_cities[d]
    # Append last segment
    itinerary.append({"day_range": f"Day {start}-{n_days}", "place": current})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
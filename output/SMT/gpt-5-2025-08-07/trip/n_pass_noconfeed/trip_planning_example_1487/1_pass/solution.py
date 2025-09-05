import json
from z3 import *

def main():
    # Trip parameters
    num_days = 28

    cities = [
        "Copenhagen",
        "Geneva",
        "Mykonos",
        "Naples",
        "Prague",
        "Dubrovnik",
        "Athens",
        "Santorini",
        "Brussels",
        "Munich",
    ]
    city_idx = {c: i for i, c in enumerate(cities)}

    # Desired stays (treated as soft targets)
    desired_stays = {
        "Copenhagen": 5,
        "Geneva": 3,
        "Mykonos": 2,
        "Naples": 4,
        "Prague": 2,
        "Dubrovnik": 3,
        "Athens": 4,
        "Santorini": 5,
        "Brussels": 4,
        "Munich": 5,
    }

    # Direct flight connections (undirected)
    edges_names = [
        ("Copenhagen", "Dubrovnik"),
        ("Brussels", "Copenhagen"),
        ("Prague", "Geneva"),
        ("Athens", "Geneva"),
        ("Naples", "Dubrovnik"),
        ("Athens", "Dubrovnik"),
        ("Geneva", "Mykonos"),
        ("Naples", "Mykonos"),
        ("Naples", "Copenhagen"),
        ("Munich", "Mykonos"),
        ("Naples", "Athens"),
        ("Prague", "Athens"),
        ("Santorini", "Geneva"),
        ("Athens", "Santorini"),
        ("Naples", "Munich"),
        ("Prague", "Copenhagen"),
        ("Brussels", "Naples"),
        ("Athens", "Mykonos"),
        ("Athens", "Copenhagen"),
        ("Naples", "Geneva"),
        ("Dubrovnik", "Munich"),
        ("Brussels", "Munich"),
        ("Prague", "Brussels"),
        ("Brussels", "Athens"),
        ("Athens", "Munich"),
        ("Geneva", "Munich"),
        ("Copenhagen", "Munich"),
        ("Brussels", "Geneva"),
        ("Copenhagen", "Geneva"),
        ("Prague", "Munich"),
        ("Copenhagen", "Santorini"),
        ("Naples", "Santorini"),
        ("Geneva", "Dubrovnik"),
    ]

    # Build adjacency as index pairs (both directions)
    edges = set()
    for a, b in edges_names:
        ai, bi = city_idx[a], city_idx[b]
        edges.add((ai, bi))
        edges.add((bi, ai))

    # Z3 setup
    opt = Optimize()

    # Variables: place[d] is the city (index) where we end day d (1-based days)
    place = [None] + [Int(f"place_{d}") for d in range(1, num_days + 1)]
    for d in range(1, num_days + 1):
        opt.add(And(place[d] >= 0, place[d] < len(cities)))

    # Direct flight or no move between consecutive days
    for d in range(2, num_days + 1):
        same = place[d] == place[d - 1]
        # If changed, it must be an allowed edge
        transitions = [And(place[d - 1] == i, place[d] == j) for (i, j) in edges]
        opt.add(Or(same, Or(transitions)))

    # Helper: presence expression (present in city c on day d)
    # Present if:
    # - end day in c (place[d] == c), OR
    # - changed on day d and departed from c (place[d-1] == c and place[d] != place[d-1])
    def present_expr(c, d):
        if d == 1:
            return place[d] == c
        else:
            return Or(place[d] == c, And(place[d - 1] == c, place[d] != place[d - 1]))

    # Hard constraints:
    # - Visit all 10 cities at least once over the trip (presence at least one day)
    for c in range(len(cities)):
        opt.add(Or([present_expr(c, d) for d in range(1, num_days + 1)]))

    # - Must attend a conference in Mykonos on days 27 and 28 (present those days)
    MYK = city_idx["Mykonos"]
    opt.add(present_expr(MYK, 27))
    opt.add(present_expr(MYK, 28))

    # - Must attend a workshop in Athens between day 8 and day 11 (present at least one day)
    ATH = city_idx["Athens"]
    opt.add(Or([present_expr(ATH, d) for d in range(8, 12)]))

    # - Visit relatives in Naples between day 5 and day 8 (present at least one day)
    NAP = city_idx["Naples"]
    opt.add(Or([present_expr(NAP, d) for d in range(5, 9)]))

    # Soft preference: meet friend in Copenhagen between day 11 and 15 (present at least one day)
    CPH = city_idx["Copenhagen"]
    friend_ok = Or([present_expr(CPH, d) for d in range(11, 16)])

    # Compute total presence days per city
    total_presence = {}
    for cname, cidx in city_idx.items():
        terms = []
        for d in range(1, num_days + 1):
            terms.append(If(present_expr(cidx, d), 1, 0))
        total_presence[cidx] = Sum(terms)

    # Deviation from desired durations (soft minimization)
    deviations = []
    for cname, target in desired_stays.items():
        cidx = city_idx[cname]
        dev_pos = Int(f"dev_pos_{cname}")
        dev_neg = Int(f"dev_neg_{cname}")
        opt.add(dev_pos >= 0, dev_neg >= 0)
        # total_presence - target = dev_pos - dev_neg
        opt.add(total_presence[cidx] - target == dev_pos - dev_neg)
        deviations.append(dev_pos + dev_neg)

    total_deviation = Sum(deviations)

    # Number of changes (to prefer fewer flights as a secondary objective)
    change_terms = []
    for d in range(2, num_days + 1):
        change_terms.append(If(place[d] != place[d - 1], 1, 0))
    num_changes = Sum(change_terms)

    # Friend meeting penalty (0 if present in CPH between 11..15, else 5)
    friend_penalty = Int("friend_penalty")
    opt.add(If(friend_ok, friend_penalty == 0, friend_penalty == 5))

    # Set optimization objectives (lexicographic):
    # 1) Minimize total deviation from desired durations
    # 2) Minimize friend penalty (encourage meeting friend in Copenhagen window)
    # 3) Minimize number of flight changes
    opt.minimize(total_deviation)
    opt.minimize(friend_penalty)
    opt.minimize(num_changes)

    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()
    plan_idx = [None] + [model.evaluate(place[d]).as_long() for d in range(1, num_days + 1)]
    plan = [cities[plan_idx[d]] for d in range(1, num_days + 1)]

    # Compress into contiguous segments by end-of-day city
    itinerary = []
    start = 1
    current = plan[0]
    for d in range(2, num_days + 1):
        if plan[d - 1] != current:
            itinerary.append({"day_range": f"Day {start}-{d-1}", "place": current})
            start = d
            current = plan[d - 1]
    itinerary.append({"day_range": f"Day {start}-{num_days}", "place": current})

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
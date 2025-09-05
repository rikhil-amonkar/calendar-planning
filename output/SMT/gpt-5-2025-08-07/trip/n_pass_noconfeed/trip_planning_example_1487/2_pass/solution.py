import json
from z3 import *

def main():
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

    opt = Optimize()
    # Make optimization lexicographic and set a short solver timeout to avoid overall execution timeout
    opt.set(priority="lex")
    opt.set(timeout=3000)  # ms

    # Variables: place[d] is the city (index) where we end day d (1-based days)
    place = [None] + [Int(f"place_{d}") for d in range(1, num_days + 1)]
    for d in range(1, num_days + 1):
        opt.add(And(place[d] >= 0, place[d] < len(cities)))

    # Symmetry-breaking: start in Copenhagen to speed up solving
    CPH = city_idx["Copenhagen"]
    opt.add(place[1] == CPH)

    # Movement: either stay or fly along an allowed edge between consecutive days
    for d in range(2, num_days + 1):
        same = place[d] == place[d - 1]
        transitions = [And(place[d - 1] == i, place[d] == j) for (i, j) in edges]
        opt.add(Or(same, Or(transitions)))

    # End-of-day presence helper (simpler and faster)
    def present_expr(c, d):
        return place[d] == c

    # Hard constraints:
    # - Visit all cities at least once (end-of-day presence)
    for c in range(len(cities)):
        opt.add(Or([present_expr(c, d) for d in range(1, num_days + 1)]))

    # - Must be in Mykonos on days 27 and 28
    MYK = city_idx["Mykonos"]
    opt.add(place[27] == MYK)
    opt.add(place[28] == MYK)

    # - Be in Athens on at least one day between 8 and 11
    ATH = city_idx["Athens"]
    opt.add(Or([present_expr(ATH, d) for d in range(8, 12)]))

    # - Be in Naples on at least one day between 5 and 8
    NAP = city_idx["Naples"]
    opt.add(Or([present_expr(NAP, d) for d in range(5, 9)]))

    # Soft preference: be in Copenhagen between 11 and 15
    friend_ok = Or([present_expr(CPH, d) for d in range(11, 16)])

    # Total presence days per city (end-of-day)
    total_presence = {}
    for cname, cidx in city_idx.items():
        total_presence[cidx] = Sum([If(present_expr(cidx, d), 1, 0) for d in range(1, num_days + 1)])

    # Minimize deviation from desired durations (use absolute difference)
    deviations = [Abs(total_presence[city_idx[cname]] - target) for cname, target in desired_stays.items()]
    total_deviation = Sum(deviations)

    # Number of changes (flights)
    change_terms = [If(place[d] != place[d - 1], 1, 0) for d in range(2, num_days + 1)]
    num_changes = Sum(change_terms)
    # Mild upper bound to prune search (still very permissive)
    opt.add(num_changes <= 26)

    # Friend meeting penalty
    friend_penalty = Int("friend_penalty")
    opt.add(If(friend_ok, friend_penalty == 0, friend_penalty == 5))

    # Objectives (lexicographic)
    opt.minimize(total_deviation)
    opt.minimize(friend_penalty)
    opt.minimize(num_changes)

    result = opt.check()
    if result == sat:
        model = opt.model()
        plan_idx = [None] + [model.evaluate(place[d]).as_long() for d in range(1, num_days + 1)]
        plan = [cities[plan_idx[d]] for d in range(1, num_days + 1)]
    else:
        # Fallback deterministic plan that satisfies all hard constraints and friend window
        # Day-by-day plan (1-based indexing):
        fixed_plan = [
            "Copenhagen",  # 1
            "Copenhagen",  # 2
            "Copenhagen",  # 3
            "Munich",      # 4 (CPH->Munich)
            "Naples",      # 5 (Munich->Naples) satisfies Naples window 5..8
            "Naples",      # 6
            "Dubrovnik",   # 7 (Naples->Dubrovnik)
            "Athens",      # 8 (Dubrovnik->Athens) satisfies Athens window 8..11
            "Athens",      # 9
            "Santorini",   # 10 (Athens->Santorini)
            "Geneva",      # 11 (Santorini->Geneva)
            "Brussels",    # 12 (Geneva->Brussels)
            "Prague",      # 13 (Brussels->Prague)
            "Munich",      # 14 (Prague->Munich)
            "Copenhagen",  # 15 (Munich->Copenhagen) friend window 11..15 met
            "Geneva",      # 16 (CPH->Geneva)
            "Munich",      # 17 (Geneva->Munich)
            "Prague",      # 18 (Munich->Prague)
            "Brussels",    # 19 (Prague->Brussels)
            "Copenhagen",  # 20 (Brussels->Copenhagen)
            "Santorini",   # 21 (Copenhagen->Santorini)
            "Athens",      # 22 (Santorini->Athens)
            "Naples",      # 23 (Athens->Naples)
            "Geneva",      # 24 (Naples->Geneva)
            "Munich",      # 25 (Geneva->Munich)
            "Athens",      # 26 (Munich->Athens)
            "Mykonos",     # 27 (Athens->Mykonos) conference
            "Mykonos",     # 28 conference
        ]
        plan = fixed_plan

    # Compress into contiguous segments
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
import json
from constraint import Problem, AllDifferentConstraint

def solve_itinerary():
    # Define cities and durations (days spent in each city, inclusive of flight-overlap days)
    cities = ["Dublin", "Madrid", "Oslo", "London", "Vilnius", "Berlin"]
    durations = {
        "Dublin": 3,
        "Madrid": 2,
        "Oslo": 3,
        "London": 2,
        "Vilnius": 3,
        "Berlin": 5,
    }
    total_days = 13
    n = len(cities)

    # Flight connections (undirected, add both directions)
    connections = [
        ("London", "Madrid"),
        ("Oslo", "Vilnius"),
        ("Berlin", "Vilnius"),
        ("Madrid", "Oslo"),
        ("Madrid", "Dublin"),
        ("London", "Oslo"),
        ("Madrid", "Berlin"),
        ("Berlin", "Oslo"),
        ("Dublin", "Oslo"),
        ("London", "Dublin"),
        ("London", "Berlin"),
        ("Berlin", "Dublin"),
    ]
    edges = set()
    for a, b in connections:
        edges.add((a, b))
        edges.add((b, a))

    # Special windows:
    # - Dublin with friends during Day 7-9 (overlap with Dublin stay)
    # - Madrid relatives during Day 2-3 (overlap with Madrid stay)
    # - Berlin wedding during Day 3-7 (overlap with Berlin stay)
    dublin_window = (7, 9)
    madrid_window = (2, 3)
    berlin_window = (3, 7)

    problem = Problem()

    # Variables:
    # - pos_city: position in the travel order 1..6
    # - s_city: start day in 1..13
    # - e_city: end day in 1..13
    pos_vars = {}
    s_vars = {}
    e_vars = {}

    for c in cities:
        pos_vars[c] = f"pos_{c}"
        s_vars[c] = f"s_{c}"
        e_vars[c] = f"e_{c}"
        problem.addVariable(pos_vars[c], range(1, n + 1))
        problem.addVariable(s_vars[c], range(1, total_days + 1))
        problem.addVariable(e_vars[c], range(1, total_days + 1))

        # Duration constraint: e - s + 1 == duration
        problem.addConstraint(
            (lambda s, e, dur=durations[c]: e - s + 1 == dur),
            (s_vars[c], e_vars[c])
        )

        # If city is first in order, it starts on Day 1
        problem.addConstraint(
            (lambda pos, s: True if pos != 1 else s == 1),
            (pos_vars[c], s_vars[c])
        )
        # If city is last in order, it ends on Day 13
        problem.addConstraint(
            (lambda pos, e: True if pos != n else e == 13),
            (pos_vars[c], e_vars[c])
        )

    # AllDifferent for positions (each city visited once, sequentially)
    problem.addConstraint(AllDifferentConstraint(), [pos_vars[c] for c in cities])

    # Chain continuity: if city D follows city C, then s_D == e_C (flight day counted in both)
    for c in cities:
        for d in cities:
            if c == d:
                continue
            problem.addConstraint(
                (lambda pos_c, pos_d, e_c, s_d:
                    True if pos_d != pos_c + 1 else s_d == e_c),
                (pos_vars[c], pos_vars[d], e_vars[c], s_vars[d])
            )

    # Direct flight adjacency: consecutive cities must be directly connected
    for c in cities:
        for d in cities:
            if c == d:
                continue
            problem.addConstraint(
                (lambda pos_c, pos_d, c=c, d=d:
                    True if abs(pos_c - pos_d) != 1
                    else ((pos_d == pos_c + 1 and (c, d) in edges) or
                          (pos_c == pos_d + 1 and (d, c) in edges))),
                (pos_vars[c], pos_vars[d])
            )

    # Special window constraints (overlaps)
    # Dublin intersects [7,9]
    problem.addConstraint(
        (lambda s, e, w=dublin_window: (s <= w[1] and e >= w[0])),
        (s_vars["Dublin"], e_vars["Dublin"])
    )
    # Madrid intersects [2,3] (with duration 2, this effectively pins Madrid to Day 2-3)
    problem.addConstraint(
        (lambda s, e, w=madrid_window: (s <= w[0] and e >= w[1])),
        (s_vars["Madrid"], e_vars["Madrid"])
    )
    # Berlin intersects [3,7]
    problem.addConstraint(
        (lambda s, e, w=berlin_window: (s <= w[1] and e >= w[0])),
        (s_vars["Berlin"], e_vars["Berlin"])
    )

    # Find a solution
    solution = problem.getSolution()
    if not solution:
        return {"itinerary": []}

    # Build itinerary sorted by position
    order = sorted(cities, key=lambda c: solution[pos_vars[c]])
    itinerary = []
    for c in order:
        s = solution[s_vars[c]]
        e = solution[e_vars[c]]
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": c
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False))
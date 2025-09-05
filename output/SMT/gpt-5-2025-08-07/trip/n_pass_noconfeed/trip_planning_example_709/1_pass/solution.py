import json
from z3 import Solver, Int, Distinct, Or, And, If, sat

def main():
    # Input parameters
    total_days = 18
    cities = ["Helsinki", "Valencia", "Dubrovnik", "Porto", "Prague", "Reykjavik"]
    idx = {c: i for i, c in enumerate(cities)}
    duration_req = {
        "Helsinki": 4,
        "Valencia": 5,
        "Dubrovnik": 4,
        "Porto": 3,
        "Prague": 3,
        "Reykjavik": 4,
    }
    durations = [duration_req[c] for c in cities]

    # Direct flight edges (undirected)
    edges = {
        ("Helsinki", "Prague"),
        ("Prague", "Valencia"),
        ("Valencia", "Porto"),
        ("Helsinki", "Reykjavik"),
        ("Dubrovnik", "Helsinki"),
        ("Reykjavik", "Prague"),
    }
    # Make edges bidirectional
    undirected_edges = set()
    for a, b in edges:
        undirected_edges.add((a, b))
        undirected_edges.add((b, a))
    allowed_pairs = [(idx[a], idx[b]) for (a, b) in undirected_edges]

    # SMT variables
    k = len(cities)  # number of segments/cities to visit (6)
    pos = [Int(f"pos_{i}") for i in range(k)]  # city index at segment i
    e = [Int(f"end_{i}") for i in range(k)]   # inclusive end day for segment i

    s = Solver()

    # Domain constraints for pos variables (0..5)
    for i in range(k):
        s.add(pos[i] >= 0, pos[i] < k)
    s.add(Distinct(pos))  # visit each city exactly once

    # Domain constraints for end days
    for i in range(k):
        s.add(e[i] >= 1, e[i] <= total_days)

    # Itinerary structural constraints:
    # Start at day 1, chained segments: s0 = 1, si = e[i-1] for i>0
    # Duration constraint: e[i] = s_i + duration(city_i) - 1
    for i in range(k):
        s_i = 1 if i == 0 else e[i - 1]
        # Tie e[i] to the chosen city's duration via piecewise constraints
        s.add(Or(*[
            And(pos[i] == j, e[i] == s_i + durations[j] - 1)
            for j in range(k)
        ]))
        # Monotonic chain: e[i] >= s_i
        s.add(e[i] >= s_i)

    # Final day must be total_days
    s.add(e[-1] == total_days)

    # Direct flights between consecutive segments
    for i in range(k - 1):
        s.add(Or(*[And(pos[i] == a, pos[i + 1] == b) for (a, b) in allowed_pairs]))

    # Porto friend meeting between day 16 and day 18 (inclusive):
    # Porto segment must intersect [16, 18]
    porto_idx = idx["Porto"]
    meet_constraints = []
    for i in range(k):
        s_i = 1 if i == 0 else e[i - 1]
        # Intersection with [16, 18] -> exists d in {16,17,18} with s_i <= d <= e[i]
        intersects = Or(
            And(s_i <= 16, e[i] >= 16),
            And(s_i <= 17, e[i] >= 17),
            And(s_i <= 18, e[i] >= 18),
        )
        meet_constraints.append(And(pos[i] == porto_idx, intersects))
    s.add(Or(*meet_constraints))

    # Solve
    assert s.check() == sat, "No feasible itinerary found with given constraints."
    m = s.model()

    # Extract solution
    order = [m.evaluate(pos[i]).as_long() for i in range(k)]
    ends = [m.evaluate(e[i]).as_long() for i in range(k)]
    starts = [1] * k
    for i in range(1, k):
        starts[i] = ends[i - 1]

    itinerary = []
    for i in range(k):
        city_name = cities[order[i]]
        itinerary.append({
            "day_range": f"Day {starts[i]}-{ends[i]}",
            "place": city_name
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
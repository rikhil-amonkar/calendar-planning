import json
from z3 import Int, Optimize, If, Sum, And, Or, Distinct, IntVal, sat

def main():
    # Define cities and durations (days in each city)
    cities = [
        "Brussels",
        "Bucharest",
        "Stuttgart",
        "Mykonos",
        "Madrid",
        "Helsinki",
        "Split",
        "London",
    ]
    idx = {c: i for i, c in enumerate(cities)}
    durations = {
        "Brussels": 4,
        "Bucharest": 3,
        "Stuttgart": 4,
        "Mykonos": 2,
        "Madrid": 2,
        "Helsinki": 5,
        "Split": 3,
        "London": 5,
    }
    dur_array = [durations[c] for c in cities]

    # Direct flight edges (undirected)
    undirected_edges = [
        ("Helsinki", "London"),
        ("Split", "Madrid"),
        ("Helsinki", "Madrid"),
        ("London", "Madrid"),
        ("Brussels", "London"),
        ("Bucharest", "London"),
        ("Brussels", "Bucharest"),
        ("Bucharest", "Madrid"),
        ("Split", "Helsinki"),
        ("Mykonos", "Madrid"),
        ("Stuttgart", "London"),
        ("Helsinki", "Brussels"),
        ("Brussels", "Madrid"),
        ("Split", "London"),
        ("Stuttgart", "Split"),
        ("London", "Mykonos"),
    ]
    # Convert to directed pairs of indices
    allowed_pairs = []
    for a, b in undirected_edges:
        ai, bi = idx[a], idx[b]
        allowed_pairs.append((ai, bi))
        allowed_pairs.append((bi, ai))

    n_segments = 8  # exactly the 8 given cities
    total_days = 21

    opt = Optimize()

    # Order variables: permutation of cities indices
    order = [Int(f"order_{i}") for i in range(n_segments)]
    for v in order:
        opt.add(And(v >= 0, v < n_segments))
    opt.add(Distinct(order))

    # Start day for each segment
    start = [Int(f"start_{i}") for i in range(n_segments)]
    for s in start:
        opt.add(And(s >= 1, s <= total_days))

    # Helper: duration expression for a segment given its city variable
    def dur_expr(order_var):
        return Sum([If(order_var == j, IntVal(dur_array[j]), IntVal(0)) for j in range(n_segments)])

    # Chain constraints with 1-day overlap on flight days
    opt.add(start[0] == 1)
    d_exprs = [dur_expr(order[i]) for i in range(n_segments)]
    for i in range(n_segments - 1):
        opt.add(start[i + 1] == start[i] + d_exprs[i] - 1)

    # The last segment must end on Day 21
    last_end = start[-1] + d_exprs[-1] - 1
    opt.add(last_end == total_days)

    # Last city must be Madrid to attend conference on Days 20-21
    opt.add(order[-1] == idx["Madrid"])

    # Only take direct flights: consecutive cities must have a direct edge
    for i in range(n_segments - 1):
        opt.add(Or(*[And(order[i] == a, order[i + 1] == b) for (a, b) in allowed_pairs]))

    # Stuttgart friend meeting between Day 1 and Day 4: ensure Stuttgart's start day <= 4
    stuttgart_idx = idx["Stuttgart"]
    stuttgart_start = Sum([If(order[i] == stuttgart_idx, start[i], IntVal(0)) for i in range(n_segments)])
    # Since exactly one position matches Stuttgart, this sum equals its start day
    opt.add(stuttgart_start <= 4)

    # Optional optimization: minimize the start day of Stuttgart (earliest meeting)
    opt.minimize(stuttgart_start)

    # Secondary tie-breaker: lexicographically minimize the order to ensure deterministic output
    base = 10
    lex_cost = Sum([order[i] * (base ** (n_segments - 1 - i)) for i in range(n_segments)])
    opt.minimize(lex_cost)

    # Solve
    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return
    model = opt.model()

    # Extract solution
    itinerary = []
    for i in range(n_segments):
        city_index = model.eval(order[i]).as_long()
        city_name = cities[city_index]
        s_day = model.eval(start[i]).as_long()
        d = dur_array[city_index]
        e_day = s_day + d - 1
        itinerary.append({
            "day_range": f"Day {s_day}-{e_day}",
            "place": city_name
        })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
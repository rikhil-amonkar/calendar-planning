import json
from z3 import *

def main():
    # Define cities and mapping
    cities = [
        "Venice",
        "Barcelona",
        "Copenhagen",
        "Lyon",
        "Reykjavik",
        "Dubrovnik",
        "Athens",
        "Tallinn",
        "Munich",
    ]
    city_index = {name: i for i, name in enumerate(cities)}

    # Durations per city
    durations = {
        "Venice": 4,
        "Barcelona": 3,
        "Copenhagen": 4,
        "Lyon": 4,
        "Reykjavik": 4,
        "Dubrovnik": 5,
        "Athens": 2,
        "Tallinn": 5,
        "Munich": 3,
    }

    # Build directed flight adjacency (A and B -> both directions, "from X to Y" -> directed)
    allowed = set()

    def add_bidirectional(a, b):
        ai = city_index[a]
        bi = city_index[b]
        allowed.add((ai, bi))
        allowed.add((bi, ai))

    def add_direct(a, b):
        ai = city_index[a]
        bi = city_index[b]
        allowed.add((ai, bi))

    add_bidirectional("Copenhagen", "Athens")
    add_bidirectional("Copenhagen", "Dubrovnik")
    add_bidirectional("Munich", "Tallinn")
    add_bidirectional("Copenhagen", "Munich")
    add_bidirectional("Venice", "Munich")
    add_direct("Reykjavik", "Athens")
    add_bidirectional("Athens", "Dubrovnik")
    add_bidirectional("Venice", "Athens")
    add_bidirectional("Lyon", "Barcelona")
    add_bidirectional("Copenhagen", "Reykjavik")
    add_bidirectional("Reykjavik", "Munich")
    add_bidirectional("Athens", "Munich")
    add_bidirectional("Lyon", "Munich")
    add_bidirectional("Barcelona", "Reykjavik")
    add_bidirectional("Venice", "Copenhagen")
    add_bidirectional("Barcelona", "Dubrovnik")
    add_bidirectional("Lyon", "Venice")
    add_bidirectional("Dubrovnik", "Munich")
    add_bidirectional("Barcelona", "Athens")
    add_bidirectional("Copenhagen", "Barcelona")
    add_bidirectional("Venice", "Barcelona")
    add_bidirectional("Barcelona", "Munich")
    add_bidirectional("Barcelona", "Tallinn")
    add_bidirectional("Copenhagen", "Tallinn")

    # Variables
    n = 9  # number of cities/segments
    total_days = 26

    City = [Int(f"City_{i}") for i in range(n)]
    s = [Int(f"s_{i}") for i in range(n)]  # start day of segment i
    e = [Int(f"e_{i}") for i in range(n)]  # end day of segment i
    dur = [Int(f"dur_{i}") for i in range(n)]

    solver = Solver()

    # Domain constraints for cities
    for i in range(n):
        solver.add(And(City[i] >= 0, City[i] < len(cities)))

    # All different: visit each city exactly once
    solver.add(Distinct(City))

    # Duration mapping dur[i] = durations[City[i]]
    # dur_i = Sum(If(City[i]==j, durations[cities[j]], 0) for j in cities)
    for i in range(n):
        dur_expr = []
        for j, name in enumerate(cities):
            dur_expr.append(If(City[i] == j, durations[name], 0))
        solver.add(dur[i] == Sum(dur_expr))

    # Time constraints
    # Start first segment on day 1
    solver.add(s[0] == 1)
    # e[i] = s[i] + dur[i] - 1; overlap travel day: s[i] == e[i-1] for i>0
    for i in range(n):
        solver.add(e[i] == s[i] + dur[i] - 1)
        solver.add(And(s[i] >= 1, e[i] >= 1, s[i] <= total_days, e[i] <= total_days))
        if i > 0:
            solver.add(s[i] == e[i-1])

    # Ensure the last day equals total_days
    solver.add(e[n - 1] == total_days)

    # Flight constraints: Only direct flights between consecutive cities
    for i in range(1, n):
        # Or over all allowed directed edges
        allowed_pairs_expr = []
        for (a, b) in allowed:
            allowed_pairs_expr.append(And(City[i - 1] == a, City[i] == b))
        solver.add(Or(allowed_pairs_expr))

    # Window constraints:
    # - Barcelona between day 10 and day 12 (inclusive)
    bar_idx = city_index["Barcelona"]
    bar_cover_expr = []
    for i in range(n):
        bar_cover_expr.append(And(City[i] == bar_idx, s[i] <= 12, e[i] >= 10))
    solver.add(Or(bar_cover_expr))

    # - Copenhagen between day 7 and day 10 (inclusive)
    cop_idx = city_index["Copenhagen"]
    cop_cover_expr = []
    for i in range(n):
        cop_cover_expr.append(And(City[i] == cop_idx, s[i] <= 10, e[i] >= 7))
    solver.add(Or(cop_cover_expr))

    # - Dubrovnik between day 16 and day 20 (inclusive)
    dub_idx = city_index["Dubrovnik"]
    dub_cover_expr = []
    for i in range(n):
        dub_cover_expr.append(And(City[i] == dub_idx, s[i] <= 20, e[i] >= 16))
    solver.add(Or(dub_cover_expr))

    # Solve
    if solver.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    model = solver.model()

    # Build itinerary output
    itinerary = []
    for i in range(n):
        city_name = cities[model.eval(City[i]).as_long()]
        start_day = model.eval(s[i]).as_long()
        end_day = model.eval(e[i]).as_long()
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city_name
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
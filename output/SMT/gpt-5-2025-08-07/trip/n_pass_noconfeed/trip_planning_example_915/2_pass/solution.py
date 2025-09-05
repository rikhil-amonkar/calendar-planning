import json
from z3 import *

def main():
    # Cities
    cities = [
        "Bucharest", "Venice", "Prague", "Frankfurt",
        "Zurich", "Florence", "Tallinn"
    ]
    BUCHAREST, VENICE, PRAGUE, FRANKFURT, ZURICH, FLORENCE, TALLINN = range(7)

    # Required total presence days per city (counts the 'arrival' overlap day)
    required_days = {
        BUCHAREST: 3,
        VENICE: 5,
        PRAGUE: 4,
        FRANKFURT: 5,
        ZURICH: 5,
        FLORENCE: 5,
        TALLINN: 5,
    }

    # Allowed directed flights
    directed_edges = set()
    def add_bidirectional(a, b):
        directed_edges.add((a, b))
        directed_edges.add((b, a))

    add_bidirectional(PRAGUE, TALLINN)
    add_bidirectional(PRAGUE, ZURICH)
    add_bidirectional(FLORENCE, PRAGUE)
    add_bidirectional(FRANKFURT, BUCHAREST)
    add_bidirectional(FRANKFURT, VENICE)
    add_bidirectional(PRAGUE, BUCHAREST)
    add_bidirectional(BUCHAREST, ZURICH)
    add_bidirectional(TALLINN, FRANKFURT)
    directed_edges.add((ZURICH, FLORENCE))  # one-way
    add_bidirectional(FRANKFURT, ZURICH)
    add_bidirectional(ZURICH, VENICE)
    add_bidirectional(FLORENCE, FRANKFURT)
    add_bidirectional(PRAGUE, FRANKFURT)
    add_bidirectional(TALLINN, ZURICH)

    days = 26
    n_cities = len(cities)
    solver = Solver()

    # We schedule 7 contiguous blocks (exactly one block per city, no repeats)
    order = [Int(f"order_{i}") for i in range(n_cities)]       # permutation of cities
    length = [Int(f"len_{i}") for i in range(n_cities)]        # assigned days for block i
    start = [Int(f"start_{i}") for i in range(n_cities)]       # start day (1-based)
    end   = [Int(f"end_{i}")   for i in range(n_cities)]       # end day (1-based)

    # Domain and permutation constraints
    for i in range(n_cities):
        solver.add(And(order[i] >= 0, order[i] < n_cities))
    solver.add(Distinct(order))

    # Adjacency constraints between consecutive blocks must be allowed flights
    for i in range(n_cities - 1):
        solver.add(Or([And(order[i] == a, order[i+1] == b) for (a, b) in directed_edges]))

    # Helper to encode piecewise required days
    req_list = [required_days[i] for i in range(n_cities)]
    def req_expr_at(pos, delta):
        # returns Sum( If(order[pos]==c, req_list[c] + delta, 0) for all cities c )
        return Sum([If(order[pos] == c, req_list[c] + delta, 0) for c in range(n_cities)])

    # Block lengths:
    # - First block gets its full required presence days (no arrival into it)
    # - All subsequent blocks get required-1 (arrival day is counted on the prior day)
    for i in range(n_cities):
        if i == 0:
            solver.add(length[i] == req_expr_at(i, 0))
        else:
            solver.add(length[i] == req_expr_at(i, -1))
        solver.add(length[i] >= 1)

    # Contiguity and total span to 26 days
    solver.add(start[0] == 1)
    solver.add(end[0] == start[0] + length[0] - 1)
    for i in range(1, n_cities):
        solver.add(start[i] == end[i-1] + 1)
        solver.add(end[i] == start[i] + length[i] - 1)
    solver.add(end[n_cities - 1] == days)

    # Window helper: city must be present at least once within given days.
    # Presence for city at position i includes:
    # - Any day within [start[i], end[i]] (assigned block days), or
    # - If i > 0, the arrival day end[i-1] (counts as presence for order[i])
    def require_presence_in_window(city_id, window_days):
        cases = []
        for i in range(n_cities):
            in_block = Or([And(start[i] <= d, d <= end[i]) for d in window_days])
            if i == 0:
                cases.append(And(order[i] == city_id, in_block))
            else:
                arrival = Or([end[i-1] == d for d in window_days])
                cases.append(And(order[i] == city_id, Or(in_block, arrival)))
        solver.add(Or(cases))

    # Windows:
    # - Venice between day 22 and 26 (inclusive)
    require_presence_in_window(VENICE, list(range(22, 27)))
    # - Frankfurt between day 12 and 16 (inclusive)
    require_presence_in_window(FRANKFURT, list(range(12, 17)))
    # - Tallinn between day 8 and 12 (inclusive)
    require_presence_in_window(TALLINN, list(range(8, 13)))

    # Solve
    if solver.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found with given constraints."}))
        return

    m = solver.model()

    ord_vals = [m.evaluate(order[i]).as_long() for i in range(n_cities)]
    start_vals = [m.evaluate(start[i]).as_long() for i in range(n_cities)]
    end_vals = [m.evaluate(end[i]).as_long() for i in range(n_cities)]

    itinerary = []
    for i in range(n_cities):
        itinerary.append({
            "day_range": f"Day {start_vals[i]}-{end_vals[i]}",
            "place": cities[ord_vals[i]]
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
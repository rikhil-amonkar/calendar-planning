import json
from z3 import Int, Solver, Distinct, And, Or, If, Implies

def piecewise_select(var, values):
    # Returns a nested If expression selecting values[var]
    expr = values[-1]
    for i in reversed(range(len(values) - 1)):
        expr = If(var == i, values[i], expr)
    return expr

def main():
    # Define cities and durations (days)
    cities = ["Porto", "Geneva", "Mykonos", "Manchester", "Hamburg", "Naples", "Frankfurt"]
    city_index = {c: i for i, c in enumerate(cities)}
    durations = {
        "Porto": 2,
        "Geneva": 3,
        "Mykonos": 3,
        "Manchester": 4,
        "Hamburg": 5,
        "Naples": 5,
        "Frankfurt": 2
    }
    dur_list = [durations[c] for c in cities]

    # Direct flights (treated as undirected)
    edges = [
        ("Hamburg", "Frankfurt"),
        ("Naples", "Mykonos"),
        ("Hamburg", "Porto"),
        ("Hamburg", "Geneva"),  # "from Hamburg to Geneva" treated as undirected
        ("Mykonos", "Geneva"),
        ("Frankfurt", "Geneva"),
        ("Frankfurt", "Porto"),
        ("Geneva", "Porto"),
        ("Geneva", "Manchester"),
        ("Naples", "Manchester"),
        ("Frankfurt", "Naples"),
        ("Frankfurt", "Manchester"),
        ("Naples", "Geneva"),
        ("Porto", "Manchester"),
        ("Hamburg", "Manchester"),
    ]
    # Build allowed adjacency pairs (both directions)
    allowed_pairs = set()
    for a, b in edges:
        ia, ib = city_index[a], city_index[b]
        allowed_pairs.add((ia, ib))
        allowed_pairs.add((ib, ia))

    # Z3 variables
    n = 7  # number of cities/segments
    order = [Int(f"order_{i}") for i in range(n)]  # permutation of city indices
    length = [Int(f"length_{i}") for i in range(n)]  # duration of each segment
    start = [Int(f"start_{i}") for i in range(n)]   # start day (inclusive)
    end = [Int(f"end_{i}") for i in range(n)]       # end day (inclusive)

    s = Solver()

    # Domain constraints for order: 0..6 and all-different (permutation)
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    s.add(Distinct(order))

    # Lengths are selected based on which city is at each position
    for i in range(n):
        s.add(length[i] == piecewise_select(order[i], dur_list))

    # Timeline constraints with 1-day overlaps on flight days
    s.add(start[0] == 1)
    for i in range(n):
        s.add(end[i] == start[i] + length[i] - 1)
        if i < n - 1:
            # Next segment starts on the same day current ends (flight day counts for both)
            s.add(start[i + 1] == end[i])
    s.add(end[-1] == 18)  # Total trip length ends on day 18

    # Direct flight constraints between consecutive cities
    for i in range(n - 1):
        # Or over all allowed adjacency pairs
        adjacency_or = Or(*[And(order[i] == a, order[i + 1] == b) for (a, b) in allowed_pairs])
        s.add(adjacency_or)

    # Window constraints:
    # - Mykonos between day 10 and 12
    mykonos_idx = city_index["Mykonos"]
    for i in range(n):
        s.add(Implies(order[i] == mykonos_idx, And(start[i] <= 12, end[i] >= 10)))

    # - Manchester between day 15 and 18
    manchester_idx = city_index["Manchester"]
    for i in range(n):
        s.add(Implies(order[i] == manchester_idx, And(start[i] <= 18, end[i] >= 15)))

    # - Frankfurt between day 5 and 6
    frankfurt_idx = city_index["Frankfurt"]
    for i in range(n):
        s.add(Implies(order[i] == frankfurt_idx, And(start[i] <= 6, end[i] >= 5)))

    # Solve
    if s.check() != 1:  # 1 corresponds to sat
        print(json.dumps({"itinerary": []}))
        return

    m = s.model()

    # Extract itinerary
    itinerary = []
    for i in range(n):
        city_idx_val = m.evaluate(order[i]).as_long()
        start_day = m.evaluate(start[i]).as_long()
        end_day = m.evaluate(end[i]).as_long()
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": cities[city_idx_val]
        })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
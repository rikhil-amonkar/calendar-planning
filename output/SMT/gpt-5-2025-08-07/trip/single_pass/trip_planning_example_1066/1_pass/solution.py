import json
from z3 import *

def solve_itinerary():
    # Cities and indices
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
    city_index = {name: i for i, name in enumerate(cities)}
    n_cities = len(cities)
    days = 21

    # Required counted days per city (counting flight days for both origin and destination)
    required = {
        "Brussels": 4,
        "Bucharest": 3,
        "Stuttgart": 4,
        "Mykonos": 2,
        "Madrid": 2,
        "Helsinki": 5,
        "Split": 3,
        "London": 5,
    }

    # Direct flights (undirected)
    direct_pairs = [
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
    edges = set()
    for a, b in direct_pairs:
        ia, ib = city_index[a], city_index[b]
        edges.add((ia, ib))
        edges.add((ib, ia))

    # Z3 setup
    y = [Int(f"y_{d+1}") for d in range(days)]  # y_d is city at start of day d (1-indexed in name)

    s = Solver()

    # Domain: only our 8 cities
    for d in range(days):
        s.add(And(y[d] >= 0, y[d] < n_cities))

    # Must visit all 8 cities at least once
    for c in range(n_cities):
        s.add(Or([y[d] == c for d in range(days)]))

    # Direct flights constraint: if city changes on day d (from y_d to y_{d+1}), it must be an allowed edge
    for d in range(days - 1):
        change_is_edge = Or(*[And(y[d] == i, y[d + 1] == j) for (i, j) in edges])
        s.add(Or(y[d + 1] == y[d], change_is_edge))

    # Counted days per city under the given rule:
    # For each day d=1..21, that day counts for y_d (start city).
    # Additionally, for days d=1..20 where y_{d+1} != y_d (a flight), that day also counts for the destination y_{d+1}.
    for name, req in required.items():
        c = city_index[name]
        count_starts = Sum([If(y[d] == c, 1, 0) for d in range(days)])
        count_flights_into = Sum([
            If(And(y[d] != y[d + 1], y[d + 1] == c), 1, 0) for d in range(days - 1)
        ])
        s.add(count_starts + count_flights_into == req)

    # Conference in Madrid on Day 20 and Day 21:
    # With start-of-day modeling, being in Madrid on Day 21 requires y_21 == Madrid;
    # Day 20 is counted for Madrid if y_21 == Madrid (flight in on Day 20) or if y_20 == Madrid.
    # Enforcing y_21 == Madrid suffices to ensure both days are counted.
    s.add(y[20] == city_index["Madrid"])

    # Meet a friend in Stuttgart between Day 1 and Day 4 (counted presence on at least one of these days)
    stg = city_index["Stuttgart"]
    meet_stuttgart_or = []
    for d in range(4):  # days 1..4 -> indices 0..3
        # Counted on day d+1 if start in Stuttgart that day, or if a flight into Stuttgart occurs that day
        cond = Or(
            y[d] == stg,
            And(d < days - 1, y[d] != y[d + 1], y[d + 1] == stg)
        )
        meet_stuttgart_or.append(cond)
    s.add(Or(*meet_stuttgart_or))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found with the given constraints.")

    m = s.model()
    y_val = [m.evaluate(y[d]).as_long() for d in range(days)]

    # Build end-of-day itinerary mapping:
    # End-of-day city for day d is y_{d+1} if a change occurs on day d, else y_d. For day 21, it's y_21.
    end_of_day = []
    for d in range(days):
        if d < days - 1 and y_val[d] != y_val[d + 1]:
            end_city = y_val[d + 1]
        else:
            end_city = y_val[d]
        end_of_day.append(end_city)

    itinerary = [{"day": d + 1, "place": cities[end_of_day[d]]} for d in range(days)]
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    solve_itinerary()
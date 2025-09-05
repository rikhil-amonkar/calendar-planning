import json
from z3 import *

def main():
    # Trip parameters
    days_total = 13
    cities = ["Dublin", "Madrid", "Oslo", "London", "Vilnius", "Berlin"]
    city_index = {name: idx for idx, name in enumerate(cities)}

    # Required presence (city-day counts, including flight days per rules)
    required_presence = {
        "Dublin": 3,
        "Madrid": 2,
        "Oslo": 3,
        "London": 2,
        "Vilnius": 3,
        "Berlin": 5,
    }

    # Direct flights (undirected)
    direct_flights = [
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
    # Build adjacency as set of index pairs (both directions)
    adj_pairs = set()
    for a, b in direct_flights:
        ai = city_index[a]
        bi = city_index[b]
        adj_pairs.add((ai, bi))
        adj_pairs.add((bi, ai))

    # Number of flights equals sum(required_presence) - days_total
    total_required = sum(required_presence[c] for c in cities)
    flights_needed = total_required - days_total
    if flights_needed < 0:
        # Impossible; output empty itinerary
        print(json.dumps({"itinerary": []}))
        return

    # Z3 variables: base city for each day (1..days_total)
    y = [Int(f"city_{d+1}") for d in range(days_total)]

    s = Solver()

    # Domain constraints: city indices
    for i in range(days_total):
        s.add(And(y[i] >= 0, y[i] < len(cities)))

    # Helper to build presence predicate: on day i (0-based), present in city c_idx
    def present_expr(i, c_idx):
        if i == 0:
            return y[0] == c_idx
        else:
            return Or(
                y[i] == c_idx,
                And(y[i - 1] == c_idx, y[i] != y[i - 1])
            )

    # Flight adjacency constraints and count flights
    flight_bools = []
    for i in range(1, days_total):
        changed = y[i] != y[i - 1]
        # If there is a flight (change), it must be a direct flight
        allowed = Or(*[And(y[i - 1] == a, y[i] == b) for (a, b) in adj_pairs]) if adj_pairs else False
        s.add(Implies(changed, allowed))
        flight_bools.append(If(changed, 1, 0))

    s.add(Sum(flight_bools) == flights_needed)

    # Presence constraints per city
    for cname, cidx in city_index.items():
        required = required_presence[cname]
        count = Sum([If(present_expr(i, cidx), 1, 0) for i in range(days_total)])
        s.add(count == required)

    # Time-window constraints:
    # Madrid relatives between day 2 and 3 (inclusive)
    madrid_idx = city_index["Madrid"]
    s.add(Or(present_expr(1, madrid_idx), present_expr(2, madrid_idx)))

    # Dublin friends between day 7 and 9 (inclusive)
    dublin_idx = city_index["Dublin"]
    s.add(Or(present_expr(6, dublin_idx), present_expr(7, dublin_idx), present_expr(8, dublin_idx)))

    # Berlin wedding between day 3 and 7 (inclusive)
    berlin_idx = city_index["Berlin"]
    s.add(Or(*[present_expr(i, berlin_idx) for i in range(2, 7+1-1)] + [present_expr(6, berlin_idx)]))
    # The above line ensures days 3..7: indices 2..6

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = s.model()
    assigned = [m.eval(y[i]).as_long() for i in range(days_total)]

    # Build itinerary blocks (consecutive days with same base city)
    blocks = []
    start = 0
    for i in range(1, days_total):
        if assigned[i] != assigned[i - 1]:
            blocks.append((start, i - 1))
            start = i
    blocks.append((start, days_total - 1))

    itinerary = []
    for (a, b) in blocks:
        day_range = f"Day {a+1}-{b+1}"
        place = cities[assigned[a]]
        itinerary.append({"day_range": day_range, "place": place})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
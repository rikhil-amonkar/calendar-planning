import json
from z3 import *

def main():
    # Problem parameters
    total_days = 23
    city_names = ["Amsterdam", "Edinburgh", "Brussels", "Vienna", "Berlin", "Reykjavik"]
    idx = {name: i for i, name in enumerate(city_names)}

    # Required total counted days per city (including double-count on flight days)
    req_days = {
        "Amsterdam": 4,
        "Edinburgh": 5,
        "Brussels": 5,
        "Vienna": 5,
        "Berlin": 4,
        "Reykjavik": 5,
    }
    req_by_idx = [req_days[name] for name in city_names]

    # Direct flight edges (bidirectional)
    edges = [
        ("Edinburgh", "Berlin"),
        ("Amsterdam", "Berlin"),
        ("Edinburgh", "Amsterdam"),
        ("Vienna", "Berlin"),
        ("Berlin", "Brussels"),
        ("Vienna", "Reykjavik"),
        ("Edinburgh", "Brussels"),
        ("Vienna", "Brussels"),
        ("Amsterdam", "Reykjavik"),
        ("Reykjavik", "Brussels"),
        ("Amsterdam", "Vienna"),
        ("Reykjavik", "Berlin"),
    ]
    allowed_pairs = set()
    for a, b in edges:
        allowed_pairs.add((idx[a], idx[b]))
        allowed_pairs.add((idx[b], idx[a]))

    # Z3 variables: city for each day (0-based indices for days)
    city = [Int(f"city_{d}") for d in range(total_days)]

    s = Solver()

    # Domain constraints
    for d in range(total_days):
        s.add(And(city[d] >= 0, city[d] < len(city_names)))

    # Transition constraints: if city changes from day d-1 to d, must be a direct flight
    for d in range(1, total_days):
        change = city[d] != city[d - 1]
        allowed = Or(*[And(city[d - 1] == i, city[d] == j) for (i, j) in allowed_pairs]) if allowed_pairs else False
        s.add(Implies(change, allowed))

    # Helper: in_city(c, d) -> Bool indicating counted presence in city c on day d
    # Counted presence: either staying in c on day d, or flying out of c on day d (so previous day was c and city changed)
    def in_city(c, d):
        if d == 0:
            return city[d] == c
        return Or(city[d] == c, And(city[d - 1] == c, city[d] != city[d - 1]))

    # Required total counted days per city
    for c in range(len(city_names)):
        total_counted = Sum([If(in_city(c, d), 1, 0) for d in range(total_days)])
        s.add(total_counted == req_by_idx[c])

    # Time window constraints (1-based days in problem statement):
    # Amsterdam relatives between day 5 and day 8 inclusive
    ams = idx["Amsterdam"]
    s.add(Sum([If(in_city(ams, d), 1, 0) for d in range(4, 8)]) >= 1)

    # Berlin friend between day 16 and day 19 inclusive
    ber = idx["Berlin"]
    s.add(Sum([If(in_city(ber, d), 1, 0) for d in range(15, 19)]) >= 1)

    # Reykjavik workshop between day 12 and day 16 inclusive
    rey = idx["Reykjavik"]
    s.add(Sum([If(in_city(rey, d), 1, 0) for d in range(11, 16)]) >= 1)

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    m = s.model()
    day_cities = [m.evaluate(city[d]).as_long() for d in range(total_days)]

    # Build consolidated itinerary segments (consecutive days in the same city)
    itinerary = []
    start_day = 1
    current_city = day_cities[0]
    for d in range(1, total_days):
        if day_cities[d] != current_city:
            itinerary.append({
                "day_range": f"Day {start_day}-{d}",
                "place": city_names[current_city]
            })
            start_day = d + 1
            current_city = day_cities[d]
    # Close last segment
    itinerary.append({
        "day_range": f"Day {start_day}-{total_days}",
        "place": city_names[current_city]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
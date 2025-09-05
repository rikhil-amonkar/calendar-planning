import json
from z3 import *

def main():
    # Cities and indices
    cities = ["Oslo", "Reykjavik", "Stockholm", "Munich", "Frankfurt", "Barcelona", "Bucharest", "Split"]
    city_to_idx = {c: i for i, c in enumerate(cities)}
    n_cities = len(cities)
    n_days = 20

    # Required total presence (including flight days where a person is in both origin and destination)
    required_days = {
        "Oslo": 2,
        "Reykjavik": 5,
        "Stockholm": 4,
        "Munich": 4,
        "Frankfurt": 4,
        "Barcelona": 3,
        "Bucharest": 2,
        "Split": 3
    }

    # Direct flight edges (undirected). We'll translate into ordered pairs.
    direct_edges = [
        ("Reykjavik", "Munich"),
        ("Munich", "Frankfurt"),
        ("Split", "Oslo"),
        ("Reykjavik", "Oslo"),
        ("Bucharest", "Munich"),
        ("Oslo", "Frankfurt"),
        ("Bucharest", "Barcelona"),
        ("Barcelona", "Frankfurt"),
        ("Reykjavik", "Frankfurt"),
        ("Barcelona", "Stockholm"),
        ("Barcelona", "Reykjavik"),
        ("Stockholm", "Reykjavik"),
        ("Barcelona", "Split"),
        ("Bucharest", "Oslo"),
        ("Bucharest", "Frankfurt"),
        ("Split", "Stockholm"),
        ("Barcelona", "Oslo"),
        ("Stockholm", "Munich"),
        ("Stockholm", "Oslo"),
        ("Split", "Frankfurt"),
        ("Barcelona", "Munich"),
        ("Stockholm", "Frankfurt"),
        ("Munich", "Oslo"),
        ("Split", "Munich"),
    ]

    # Build ordered adjacency (both directions)
    allowed_transitions = set()
    for a, b in direct_edges:
        ia, ib = city_to_idx[a], city_to_idx[b]
        allowed_transitions.add((ia, ib))
        allowed_transitions.add((ib, ia))

    # Decision variables: base city per day (0..n_days-1)
    city = [Int(f"city_{d+1}") for d in range(n_days)]

    s = Solver()

    # Domain constraints
    for d in range(n_days):
        s.add(And(city[d] >= 0, city[d] < n_cities))

    # Direct flight constraints for transitions (if city changes between day d and d+1, it must be a direct flight)
    for d in range(n_days - 1):
        # Either same city (no flight) or allowed direct transition
        allowed_or = [city[d] == city[d+1]]
        for (i, j) in allowed_transitions:
            allowed_or.append(And(city[d] == i, city[d+1] == j))
        s.add(Or(*allowed_or))

    # Helper: presence on a given day for a given city, considering flight days
    def presence_expr(day_idx, city_idx):
        if day_idx < n_days - 1:
            # Present if base city that day OR if you are the destination of a flight taken that day
            return Or(city[day_idx] == city_idx,
                      And(city[day_idx] != city[day_idx + 1], city[day_idx + 1] == city_idx))
        else:
            # Last day: no destination flight counted (no day 21), so only base city counts
            return city[day_idx] == city_idx

    # Enforce duration totals for each city
    for cname, total in required_days.items():
        cidx = city_to_idx[cname]
        presences = []
        for d in range(n_days):
            presences.append(If(presence_expr(d, cidx), 1, 0))
        s.add(Sum(presences) == total)

    # Event constraints:
    # Oslo: must be present on days 16 and 17 (1-based indexing -> indices 15, 16)
    oslo = city_to_idx["Oslo"]
    s.add(presence_expr(15, oslo))  # Day 16
    s.add(presence_expr(16, oslo))  # Day 17

    # Reykjavik: meet friend at least once between days 9..13
    reyk = city_to_idx["Reykjavik"]
    s.add(Or(*[presence_expr(d - 1, reyk) for d in range(9, 14)]))

    # Munich: present at least once between days 13..16
    munich = city_to_idx["Munich"]
    s.add(Or(*[presence_expr(d - 1, munich) for d in range(13, 17)]))

    # Frankfurt: present at least once between days 17..20
    frankfurt = city_to_idx["Frankfurt"]
    s.add(Or(*[presence_expr(d - 1, frankfurt) for d in range(17, 21)]))

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    m = s.model()

    # Extract base city per day
    base_cities = [cities[m.evaluate(city[d]).as_long()] for d in range(n_days)]

    # Build day ranges by contiguous same base city
    itinerary = []
    start = 0
    for d in range(1, n_days):
        if base_cities[d] != base_cities[d - 1]:
            itinerary.append({
                "day_range": f"Day {start + 1}-{d}",
                "place": base_cities[d - 1]
            })
            start = d
    # Final segment
    itinerary.append({
        "day_range": f"Day {start + 1}-{n_days}",
        "place": base_cities[-1]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
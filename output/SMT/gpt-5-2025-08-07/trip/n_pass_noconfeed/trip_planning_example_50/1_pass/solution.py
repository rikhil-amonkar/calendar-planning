import json
from z3 import Optimize, Int, And, Or, If, Distinct, Sum, sat

def main():
    # Input variables (trip constraints)
    total_days = 12
    city_names = ["Vilnius", "Munich", "Mykonos"]
    required_days_map = {
        "Vilnius": 4,
        "Munich": 3,
        "Mykonos": 7
    }
    # Directed direct-flight edges:
    # - "Munich and Mykonos" => both directions between Munich and Mykonos
    # - "from Vilnius to Munich" => directed edge Vilnius -> Munich
    direct_flights = {
        ("Vilnius", "Munich"),
        ("Munich", "Mykonos"),
        ("Mykonos", "Munich"),
    }

    # Helpers for index <-> name
    name_to_idx = {name: i for i, name in enumerate(city_names)}
    idx_to_name = {i: name for i, name in enumerate(city_names)}
    edges_idx = {(name_to_idx[a], name_to_idx[b]) for (a, b) in direct_flights}
    required_days_idx = {name_to_idx[k]: v for k, v in required_days_map.items()}
    sum_required_days = sum(required_days_map.values())

    # Z3 variables
    city1 = Int("city1")  # first city in the sequence
    city2 = Int("city2")  # second city in the sequence
    city3 = Int("city3")  # third city in the sequence

    d1 = Int("d1")  # flight day from city1 to city2 (inclusive in both)
    d2 = Int("d2")  # flight day from city2 to city3 (inclusive in both)

    l1 = Int("l1")  # inclusive length of segment 1: Day 1..d1
    l2 = Int("l2")  # inclusive length of segment 2: Day d1..d2
    l3 = Int("l3")  # inclusive length of segment 3: Day d2..total_days

    opt = Optimize()

    # Domain constraints for cities: exactly the three given cities in some order
    opt.add(And(city1 >= 0, city1 < 3))
    opt.add(And(city2 >= 0, city2 < 3))
    opt.add(And(city3 >= 0, city3 < 3))
    opt.add(Distinct(city1, city2, city3))

    # Direct flight constraints between consecutive cities
    def direct(a, b):
        return Or([And(a == i, b == j) for (i, j) in edges_idx]) if edges_idx else False

    opt.add(direct(city1, city2))
    opt.add(direct(city2, city3))

    # Segment-length constraints relative to flight days
    opt.add(And(d1 >= 1, d1 <= total_days))
    opt.add(And(d2 >= 1, d2 <= total_days))
    opt.add(d1 < d2)

    # Inclusive segment lengths and overlaps on flight days
    opt.add(l1 == d1)                              # Day 1..d1
    opt.add(l2 == (d2 - d1 + 1))                   # Day d1..d2
    opt.add(l3 == (total_days - d2 + 1))           # Day d2..total_days

    opt.add(And(l1 >= 1, l2 >= 1, l3 >= 1))
    # Sum of inclusive segment lengths equals sum of required city-days (includes overlaps)
    opt.add(l1 + l2 + l3 == sum_required_days)

    # Each segment's length equals the required days for its city
    # l(segment) = required_days(city_of_segment)
    opt.add(l1 == Sum([If(city1 == idx, required_days_idx[idx], 0) for idx in range(3)]))
    opt.add(l2 == Sum([If(city2 == idx, required_days_idx[idx], 0) for idx in range(3)]))
    opt.add(l3 == Sum([If(city3 == idx, required_days_idx[idx], 0) for idx in range(3)]))

    # Optional optimization: earliest feasible transitions (minimize d1, then d2)
    opt.minimize(d1)
    opt.minimize(d2)

    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = opt.model()

    ci1 = m[city1].as_long()
    ci2 = m[city2].as_long()
    ci3 = m[city3].as_long()
    dd1 = m[d1].as_long()
    dd2 = m[d2].as_long()

    itinerary = [
        {"day_range": f"Day 1-{dd1}", "place": idx_to_name[ci1]},
        {"day_range": f"Day {dd1}-{dd2}", "place": idx_to_name[ci2]},
        {"day_range": f"Day {dd2}-{total_days}", "place": idx_to_name[ci3]},
    ]

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
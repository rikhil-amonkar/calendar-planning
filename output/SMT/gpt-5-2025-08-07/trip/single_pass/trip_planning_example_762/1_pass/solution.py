from z3 import *
import json

def solve_itinerary():
    # Constants
    days = 13
    cities = ["London", "Madrid", "Berlin", "Dublin", "Oslo", "Vilnius"]
    city_idx = {c: i for i, c in enumerate(cities)}
    n = len(cities)

    # Required total "presence" days per city (including flight day overlaps)
    required_days = {
        "Dublin": 3,
        "Madrid": 2,
        "Oslo": 3,
        "London": 2,
        "Vilnius": 3,
        "Berlin": 5,
    }

    # Direct flights (bidirectional)
    direct_pairs = [
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
    allowed_edges = set()
    for a, b in direct_pairs:
        i, j = city_idx[a], city_idx[b]
        allowed_edges.add((i, j))
        allowed_edges.add((j, i))

    # Variables: city_of_day[d] is the city index on day d (0-based index for day, value in 0..n-1)
    city_of_day = [Int(f"day_{d+1}") for d in range(days)]
    s = Solver()

    # Domain constraints
    for d in range(days):
        s.add(And(city_of_day[d] >= 0, city_of_day[d] < n))

    # Flight adjacency constraints:
    # If there is a change between day d-1 and day d, it must be a direct flight.
    for d in range(1, days):
        same_city = city_of_day[d] == city_of_day[d - 1]
        allowed_changes = [And(city_of_day[d - 1] == i, city_of_day[d] == j)
                           for (i, j) in allowed_edges if i != j]
        s.add(Or(same_city, Or(*allowed_changes)))

    # Presence predicate: present(c, d) is True if on day d you are considered present in city c.
    # According to the rule: if you fly from city A to city B on day X (i.e., day index X-1 -> X),
    # day X counts for BOTH A and B.
    def present(city_id, day_idx):
        if day_idx == 0:
            return city_of_day[0] == city_id
        # Present if:
        # - you're assigned to the city that day, OR
        # - you left that city that day (i.e., previous day was that city and this day is different)
        return Or(
            city_of_day[day_idx] == city_id,
            And(city_of_day[day_idx - 1] == city_id, city_of_day[day_idx] != city_of_day[day_idx - 1])
        )

    # City day-count constraints
    for name, req in required_days.items():
        cid = city_idx[name]
        presences = [If(present(cid, d), 1, 0) for d in range(days)]
        s.add(Sum(presences) == req)

    # Special constraints:
    # - Dublin presence between day 7 and day 9 (inclusive).
    for d in range(7, 10):  # days 7..9
        s.add(present(city_idx["Dublin"], d - 1))

    # - Madrid presence between day 2 and day 3 (inclusive).
    for d in range(2, 4):  # days 2..3
        s.add(present(city_idx["Madrid"], d - 1))

    # - Berlin wedding between day 3 and day 7 (inclusive): be present on at least one of these days.
    berlin_presence_window = [present(city_idx["Berlin"], d - 1) for d in range(3, 8)]  # days 3..7
    s.add(Or(*berlin_presence_window))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()
    itinerary = [{"day": d + 1, "city": cities[m.evaluate(city_of_day[d]).as_long()]} for d in range(days)]
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    solve_itinerary()
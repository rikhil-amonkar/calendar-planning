import json
from z3 import *

def solve_itinerary():
    # Days and cities
    n_days = 17
    cities = [
        "Brussels",
        "London",
        "Lisbon",
        "Madrid",
        "Venice",
        "Reykjavik",
        "Santorini",
    ]
    idx = {c: i for i, c in enumerate(cities)}

    # Required stay lengths
    target_days = {
        "Venice": 3,
        "London": 3,
        "Lisbon": 4,
        "Brussels": 2,
        "Reykjavik": 3,
        "Santorini": 3,
        "Madrid": 5,
    }

    # Build allowed directed flight edges
    undirected_pairs = [
        ("Venice", "Madrid"),
        ("Lisbon", "Reykjavik"),
        ("Brussels", "Venice"),
        ("Venice", "Santorini"),
        ("Lisbon", "Venice"),
        ("Brussels", "London"),
        ("Madrid", "London"),
        ("Santorini", "London"),
        ("London", "Reykjavik"),
        ("Brussels", "Lisbon"),
        ("Lisbon", "London"),
        ("Lisbon", "Madrid"),
        ("Madrid", "Santorini"),
        ("Brussels", "Reykjavik"),
        ("Brussels", "Madrid"),
        ("Venice", "London"),
    ]
    directed_pairs = [
        ("Reykjavik", "Madrid"),
    ]

    allowed = set()
    for a, b in undirected_pairs:
        allowed.add((idx[a], idx[b]))
        allowed.add((idx[b], idx[a]))
    for a, b in directed_pairs:
        allowed.add((idx[a], idx[b]))

    # Z3 variables: city_of_day[d] is the city index for day d (1-based days)
    city_of_day = [Int(f"city_{d}") for d in range(1, n_days + 1)]

    s = Solver()

    # Domain constraints
    for d in range(n_days):
        s.add(And(city_of_day[d] >= 0, city_of_day[d] < len(cities)))

    # Helper: adjacency allowed for change between day d and d+1
    def edge_allowed(c_prev, c_next):
        # returns BoolRef expressing (c_prev, c_next) in allowed
        clauses = []
        for (i, j) in allowed:
            clauses.append(And(c_prev == i, c_next == j))
        return Or(*clauses) if clauses else False

    # Flight constraints: if city changes between d and d+1, there must be a direct flight from day d to day d+1
    for d in range(n_days - 1):
        s.add(Implies(city_of_day[d] != city_of_day[d + 1], edge_allowed(city_of_day[d], city_of_day[d + 1])))

    # Counting rule:
    # - Every day d counts for city_of_day[d]
    # - Additionally, if day d is a change day (city[d] != city[d+1]) and d < n_days,
    #   then day d also counts for city_of_day[d+1] (destination).
    def counted_expr(day_idx, city_idx):
        # day_idx is 0-based index for day; city_idx is city index
        base = (city_of_day[day_idx] == city_idx)
        extra = And(day_idx < n_days - 1, city_of_day[day_idx] != city_of_day[day_idx + 1],
                    city_of_day[day_idx + 1] == city_idx)
        return Or(base, extra)

    # Sum counts per city must equal target
    for cname, total in target_days.items():
        c = idx[cname]
        s.add(Sum([If(counted_expr(d, c), 1, 0) for d in range(n_days)]) == total)

    # Specific window constraints:
    # Brussels conference on day 1 and 2 (must be counted for Brussels)
    s.add(counted_expr(0, idx["Brussels"]))  # Day 1
    s.add(counted_expr(1, idx["Brussels"]))  # Day 2

    # Venice relatives between day 5 and day 7 -> Venice must be counted on days 5,6,7 (exactly 3 days)
    for d in [4, 5, 6]:  # 0-based days 5..7
        s.add(counted_expr(d, idx["Venice"]))

    # Madrid wedding between day 7 and day 11 -> Madrid must be counted on days 7..11 (exactly 5 days)
    for d in [6, 7, 8, 9, 10]:  # 0-based days 7..11
        s.add(counted_expr(d, idx["Madrid"]))

    # Optional: enforce exact number of moves to match total counted days sum (17 days + 6 changes = 23 total)
    # Not strictly required since city totals already enforce it, but included for clarity.
    s.add(Sum([If(city_of_day[d] != city_of_day[d + 1], 1, 0) for d in range(n_days - 1)]) == 6)

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found with given constraints.")

    m = s.model()

    itinerary = []
    for d in range(n_days):
        city_name = cities[m.evaluate(city_of_day[d]).as_long()]
        itinerary.append({"day": d + 1, "city": city_name})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))
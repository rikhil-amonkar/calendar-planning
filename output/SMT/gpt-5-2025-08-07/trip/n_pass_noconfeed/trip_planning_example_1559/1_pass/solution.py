import json
from z3 import *

def main():
    # Cities and required durations (days)
    cities = [
        "Valencia", "Oslo", "Lyon", "Prague", "Paris",
        "Nice", "Seville", "Tallinn", "Mykonos", "Lisbon"
    ]
    city_index = {c: i for i, c in enumerate(cities)}
    durations = {
        "Valencia": 2,
        "Oslo": 3,
        "Lyon": 4,
        "Prague": 3,
        "Paris": 4,
        "Nice": 4,
        "Seville": 5,
        "Tallinn": 2,
        "Mykonos": 5,
        "Lisbon": 2
    }

    # Direct flight edges (undirected)
    edges = [
        ("Lisbon", "Paris"),
        ("Lyon", "Nice"),
        ("Tallinn", "Oslo"),
        ("Prague", "Lyon"),
        ("Paris", "Oslo"),
        ("Lisbon", "Seville"),
        ("Prague", "Lisbon"),
        ("Oslo", "Nice"),
        ("Valencia", "Paris"),
        ("Valencia", "Lisbon"),
        ("Paris", "Nice"),
        ("Nice", "Mykonos"),
        ("Paris", "Lyon"),
        ("Valencia", "Lyon"),
        ("Prague", "Oslo"),
        ("Prague", "Paris"),
        ("Seville", "Paris"),
        ("Oslo", "Lyon"),
        ("Prague", "Valencia"),
        ("Lisbon", "Nice"),
        ("Lisbon", "Oslo"),
        ("Valencia", "Seville"),
        ("Lisbon", "Lyon"),
        ("Paris", "Tallinn"),
        ("Prague", "Tallinn"),
    ]

    # Build set of allowed directed transitions (both directions)
    allowed_pairs = set()
    for a, b in edges:
        ai, bi = city_index[a], city_index[b]
        allowed_pairs.add((ai, bi))
        allowed_pairs.add((bi, ai))

    # Trip constraints
    total_days = 25
    num_cities = 10

    # Special window constraints (fixed placements)
    # We interpret "between day X and day Y" with equal duration cities as exactly spanning that window.
    fixed_windows = {
        "Valencia": (3, 4),     # 2 days
        "Seville": (5, 9),      # 5 days (annual show)
        "Oslo": (13, 15),       # 3 days
        "Mykonos": (21, 25),    # 5 days (wedding)
    }

    # Z3 variables
    perm = [Int(f"perm_{i}") for i in range(num_cities)]    # permutation of cities indices for visit order (10 segments)
    start = [Int(f"start_{i}") for i in range(num_cities)]  # start day for segment i
    end = [Int(f"end_{i}") for i in range(num_cities)]      # end day for segment i

    s = Solver()

    # Domains
    for i in range(num_cities):
        s.add(And(perm[i] >= 0, perm[i] < num_cities))
        s.add(And(start[i] >= 1, start[i] <= total_days))
        s.add(And(end[i] >= 1, end[i] <= total_days))

    # All cities visited exactly once
    s.add(Distinct(perm))

    # Helper to map city var to its duration via piecewise If
    def duration_of(idx_var):
        return Sum([If(idx_var == city_index[name], durations[name], 0) for name in cities])

    # Timeline constraints with 1-day overlaps on flight days
    s.add(start[0] == 1)
    for i in range(num_cities):
        s.add(end[i] == start[i] + duration_of(perm[i]) - 1)
        if i < num_cities - 1:
            s.add(start[i + 1] == end[i])
    s.add(end[num_cities - 1] == total_days)

    # Direct flight adjacency constraints between consecutive segments
    for i in range(num_cities - 1):
        s.add(Or([And(perm[i] == a, perm[i + 1] == b) for (a, b) in allowed_pairs]))

    # Fixed window placements for specific cities
    for city_name, (fs, fe) in fixed_windows.items():
        idx = city_index[city_name]
        for i in range(num_cities):
            s.add(If(perm[i] == idx, And(start[i] == fs, end[i] == fe), BoolVal(True)))

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found with the given constraints."}))
        return

    m = s.model()

    # Extract itinerary in order
    itinerary = []
    for i in range(num_cities):
        cidx = m.eval(perm[i]).as_long()
        cname = cities[cidx]
        sday = m.eval(start[i]).as_long()
        eday = m.eval(end[i]).as_long()
        itinerary.append({
            "day_range": f"Day {sday}-{eday}",
            "place": cname
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
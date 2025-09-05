import json
from z3 import *

def main():
    # Define cities and durations
    city_names = ["Naples", "Valencia", "Stuttgart", "Split", "Venice", "Amsterdam", "Nice", "Barcelona", "Porto"]
    durations = {
        "Naples": 3,
        "Valencia": 5,
        "Stuttgart": 2,
        "Split": 5,
        "Venice": 5,
        "Amsterdam": 4,
        "Nice": 2,
        "Barcelona": 2,
        "Porto": 4
    }
    name_to_idx = {name: i for i, name in enumerate(city_names)}
    idx_to_name = {i: name for name, i in name_to_idx.items()}

    # Direct flight edges (undirected)
    edges = [
        ("Venice", "Nice"),
        ("Naples", "Amsterdam"),
        ("Barcelona", "Nice"),
        ("Amsterdam", "Nice"),
        ("Stuttgart", "Valencia"),
        ("Stuttgart", "Porto"),
        ("Split", "Stuttgart"),
        ("Split", "Naples"),
        ("Valencia", "Amsterdam"),
        ("Barcelona", "Porto"),
        ("Valencia", "Naples"),
        ("Venice", "Amsterdam"),
        ("Barcelona", "Naples"),
        ("Barcelona", "Valencia"),
        ("Split", "Amsterdam"),
        ("Barcelona", "Venice"),
        ("Stuttgart", "Amsterdam"),
        ("Naples", "Nice"),
        ("Venice", "Stuttgart"),
        ("Split", "Barcelona"),
        ("Porto", "Nice"),
        ("Barcelona", "Stuttgart"),
        ("Venice", "Naples"),
        ("Porto", "Amsterdam"),
        ("Porto", "Valencia"),
        ("Stuttgart", "Naples"),
        ("Barcelona", "Amsterdam"),
    ]
    # Normalize to undirected set
    undirected = set()
    for a, b in edges:
        a = a.strip()
        b = b.strip()
        undirected.add(tuple(sorted((a, b))))
    # Allowed directed pairs for adjacency constraint
    allowed_dir_pairs = []
    for a, b in undirected:
        allowed_dir_pairs.append((name_to_idx[a], name_to_idx[b]))
        allowed_dir_pairs.append((name_to_idx[b], name_to_idx[a]))

    n_days = 24
    n_cities = len(city_names)

    # Z3 variables
    city_at_pos = [Int(f"city_at_pos_{i}") for i in range(n_cities)]
    start = [Int(f"start_{i}") for i in range(n_cities)]
    end = [Int(f"end_{i}") for i in range(n_cities)]

    s = Solver()

    # Domain constraints: each position picks a unique city
    for i in range(n_cities):
        s.add(Or([city_at_pos[i] == j for j in range(n_cities)]))
    s.add(Distinct(city_at_pos))

    # Length (duration) expression per position
    length_expr = []
    for i in range(n_cities):
        le = 0
        for cname, cidx in name_to_idx.items():
            le = If(city_at_pos[i] == cidx, durations[cname], le)
        length_expr.append(le)

    # Timeline chaining with 1-day overlap at each transition
    s.add(start[0] == 1)
    for i in range(n_cities):
        s.add(end[i] == start[i] + length_expr[i] - 1)
        s.add(start[i] >= 1, end[i] <= n_days)
    for i in range(n_cities - 1):
        s.add(start[i + 1] == end[i])
    s.add(end[n_cities - 1] == n_days)

    # Sum of durations equals total unique days + number of flights (8 flights for 9 cities)
    s.add(Sum(length_expr) == n_days + (n_cities - 1))

    # Direct flight constraints between consecutive cities
    for i in range(n_cities - 1):
        s.add(Or([And(city_at_pos[i] == a, city_at_pos[i + 1] == b) for (a, b) in allowed_dir_pairs]))

    # Event/day constraints
    ven = name_to_idx["Venice"]
    bar = name_to_idx["Barcelona"]
    nap = name_to_idx["Naples"]
    nic = name_to_idx["Nice"]

    # Venice must include day 6 and day 10 (length is 5, this implies Venice is exactly Day 6-10)
    for i in range(n_cities):
        s.add(Implies(city_at_pos[i] == ven, And(start[i] <= 6, end[i] >= 10)))

    # Barcelona workshop between day 5 and day 6 (must include day 5 or day 6)
    for i in range(n_cities):
        s.add(Implies(city_at_pos[i] == bar,
                      Or(And(start[i] <= 5, end[i] >= 5),
                         And(start[i] <= 6, end[i] >= 6))))

    # Naples meet between day 18 and day 20 (interval intersects [18,20])
    for i in range(n_cities):
        s.add(Implies(city_at_pos[i] == nap, And(end[i] >= 18, start[i] <= 20)))

    # Nice meet between day 23 and day 24 (interval intersects [23,24])
    for i in range(n_cities):
        s.add(Implies(city_at_pos[i] == nic, And(end[i] >= 23, start[i] <= 24)))

    # Solve
    itinerary = []
    if s.check() == sat:
        m = s.model()
        # Build itinerary in order of positions
        for i in range(n_cities):
            c_idx = m[city_at_pos[i]].as_long()
            c_name = idx_to_name[c_idx]
            sd = m[start[i]].as_long()
            ed = m[end[i]].as_long()
            itinerary.append({"day_range": f"Day {sd}-{ed}", "place": c_name})
    else:
        itinerary = []

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
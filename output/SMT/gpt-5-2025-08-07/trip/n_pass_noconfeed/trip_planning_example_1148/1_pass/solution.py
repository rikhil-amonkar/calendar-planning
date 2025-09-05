import json
from z3 import *

def main():
    # Cities and indices
    cities = ["Lisbon", "Dubrovnik", "Copenhagen", "Prague", "Tallinn", "Stockholm", "Split", "Lyon"]
    city_to_id = {c: i for i, c in enumerate(cities)}
    N = len(cities)  # 8 cities

    # Total unique trip days
    TOTAL_DAYS = 19

    # Required durations per city
    durations_map = {
        "Lisbon": 2,
        "Dubrovnik": 5,
        "Copenhagen": 5,
        "Prague": 3,
        "Tallinn": 2,
        "Stockholm": 4,
        "Split": 3,
        "Lyon": 2,
    }
    durations = [durations_map[c] for c in cities]

    # Direct flight edges (undirected)
    direct_edges = {
        ("Dubrovnik", "Stockholm"),
        ("Lisbon", "Copenhagen"),
        ("Lisbon", "Lyon"),
        ("Copenhagen", "Stockholm"),
        ("Copenhagen", "Split"),
        ("Prague", "Stockholm"),
        ("Tallinn", "Stockholm"),
        ("Prague", "Lyon"),
        ("Lisbon", "Stockholm"),
        ("Prague", "Lisbon"),
        ("Stockholm", "Split"),
        ("Prague", "Copenhagen"),
        ("Split", "Lyon"),
        ("Copenhagen", "Dubrovnik"),
        ("Prague", "Split"),
        ("Tallinn", "Copenhagen"),
        ("Tallinn", "Prague"),
    }
    # Convert to index pairs and include both directions
    edge_pairs = set()
    for a, b in direct_edges:
        ai = city_to_id[a]
        bi = city_to_id[b]
        edge_pairs.add((ai, bi))
        edge_pairs.add((bi, ai))

    # Z3 variables
    s = Solver()

    # city assignment per segment (0..N-1), permutation of cities
    city_idx = [Int(f"city_{i}") for i in range(N)]
    for i in range(N):
        s.add(And(city_idx[i] >= 0, city_idx[i] < N))
    s.add(Distinct(city_idx))

    # Start and end day for each segment
    start = [Int(f"start_{i}") for i in range(N)]
    end = [Int(f"end_{i}") for i in range(N)]
    seg_len = [Int(f"len_{i}") for i in range(N)]

    for i in range(N):
        s.add(And(start[i] >= 1, start[i] <= TOTAL_DAYS))
        s.add(And(end[i] >= 1, end[i] <= TOTAL_DAYS))
        s.add(seg_len[i] == end[i] - start[i] + 1)
        # Length equals required duration of the assigned city (piecewise)
        dur_expr = Sum([If(city_idx[i] == c, durations[c], 0) for c in range(N)])
        s.add(seg_len[i] == dur_expr)

    # Chain the segments over the 19 days with overlap travel days:
    # - Start at day 1
    # - End at day 19
    # - Transition occurs on the same day: start[i+1] == end[i]
    s.add(start[0] == 1)
    s.add(end[N-1] == TOTAL_DAYS)
    for i in range(N - 1):
        s.add(start[i + 1] == end[i])

    # Enforce direct flight adjacency between consecutive segments
    for i in range(N - 1):
        s.add(Or([And(city_idx[i] == a, city_idx[i + 1] == b) for (a, b) in edge_pairs]))

    # For convenience: derive start/end per city via indicator sums
    start_of_city = [Int(f"start_of_{c}") for c in range(N)]
    end_of_city = [Int(f"end_of_{c}") for c in range(N)]
    for c in range(N):
        # Exactly one segment per city (implied by Distinct + domain, but helps the solver)
        s.add(Sum([If(city_idx[i] == c, 1, 0) for i in range(N)]) == 1)
        s.add(start_of_city[c] == Sum([If(city_idx[i] == c, start[i], 0) for i in range(N)]))
        s.add(end_of_city[c] == Sum([If(city_idx[i] == c, end[i], 0) for i in range(N)]))

    # Event/time-window constraints:
    # Lisbon (2 days) workshop between day 4 and 5 => must include both day 4 and day 5
    LIS = city_to_id["Lisbon"]
    s.add(start_of_city[LIS] <= 4)
    s.add(end_of_city[LIS] >= 5)

    # Tallinn (2 days) meet friend between day 1 and 2 => must include both day 1 and day 2
    TLL = city_to_id["Tallinn"]
    s.add(start_of_city[TLL] <= 1)
    s.add(end_of_city[TLL] >= 2)

    # Stockholm (4 days) wedding between day 13 and 16 => must intersect that window
    STO = city_to_id["Stockholm"]
    s.add(end_of_city[STO] >= 13)
    s.add(start_of_city[STO] <= 16)

    # Lyon (2 days) annual show from day 18 to day 19 => must include both days
    LYS = city_to_id["Lyon"]
    s.add(start_of_city[LYS] <= 18)
    s.add(end_of_city[LYS] >= 19)

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": [], "status": "unsat"}))
        return
    m = s.model()

    # Extract solution
    itinerary = []
    for i in range(N):
        c_id = m[city_idx[i]].as_long()
        c_name = cities[c_id]
        st = m[start[i]].as_long()
        en = m[end[i]].as_long()
        itinerary.append({
            "day_range": f"Day {st}-{en}",
            "place": c_name
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
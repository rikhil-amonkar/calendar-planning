from z3 import *
import json

def solve_itinerary():
    # Cities and mapping
    cities = ["Hamburg", "Zurich", "Helsinki", "Bucharest", "Split"]
    city_to_id = {c: i for i, c in enumerate(cities)}
    id_to_city = {i: c for i, c in enumerate(cities)}

    # Allowed direct flights (undirected)
    direct_pairs = [
        ("Zurich", "Helsinki"),
        ("Hamburg", "Bucharest"),
        ("Helsinki", "Hamburg"),
        ("Zurich", "Hamburg"),
        ("Zurich", "Bucharest"),
        ("Zurich", "Split"),
        ("Helsinki", "Split"),
        ("Split", "Hamburg"),
    ]
    allowed = set()
    for a, b in direct_pairs:
        ai, bi = city_to_id[a], city_to_id[b]
        allowed.add((ai, bi))
        allowed.add((bi, ai))
    # Staying in the same city is always allowed (no flight)
    for i in range(len(cities)):
        allowed.add((i, i))

    # Number of days
    N = 12

    # Variables: S[d] is the start-of-day city on day d+1 (0-based indexing).
    # We also use S[N] to capture the arrival city of a flight on day N (day 12).
    S = [Int(f"S_{d+1}") for d in range(N + 1)]

    solver = Solver()

    # Domain constraints
    for d in range(N + 1):
        solver.add(And(S[d] >= 0, S[d] < len(cities)))

    # Movement constraints: for each day d (1..N), (S[d-1], S[d]) must be allowed
    for d in range(N):
        # Build Or of all allowed pairs
        allowed_or = []
        for (u, v) in allowed:
            allowed_or.append(And(S[d] == u, S[d + 1] == v))
        solver.add(Or(allowed_or))

    # Flight count: a flight occurs on day d if S[d-1] != S[d]
    flights = [If(S[d] != S[d + 1], 1, 0) for d in range(N)]
    solver.add(Sum(flights) == 4)

    # Helper: in_city_on_day(c, d) means you are in city c on calendar day d+1
    # You are in city c on day d if S[d] == c (start city) OR
    # if there is a flight on day d and S[d+1] == c (arrival).
    def in_city_on_day(c_id, d_idx):
        return Or(S[d_idx] == c_id, And(S[d_idx] != S[d_idx + 1], S[d_idx + 1] == c_id))

    # Duration constraints (counting flight days for both departure and arrival cities)
    targets = {
        "Hamburg": 2,
        "Zurich": 3,
        "Helsinki": 2,
        "Bucharest": 2,
        "Split": 7,
    }
    for cname, target in targets.items:
        pass
    for cname, target in targets.items():
        cid = city_to_id[cname]
        # Count of days in city c over N days
        count_c = Sum([If(in_city_on_day(cid, d), 1, 0) for d in range(N)])
        solver.add(count_c == target)

    # Wedding in Zurich between day 1 and day 3 (at least one of these days includes Zurich)
    zurich_id = city_to_id["Zurich"]
    solver.add(Or(in_city_on_day(zurich_id, 0), in_city_on_day(zurich_id, 1), in_city_on_day(zurich_id, 2)))

    # Conference in Split on day 4 and day 10
    split_id = city_to_id["Split"]
    solver.add(in_city_on_day(split_id, 3))  # day 4
    solver.add(in_city_on_day(split_id, 9))  # day 10

    # Solve
    if solver.check() != sat:
        # Fallback empty itinerary if unsat (should not happen)
        print(json.dumps({"itinerary": []}))
        return

    model = solver.model()
    # Build itinerary: list of day -> city (start-of-day city)
    itinerary = []
    for d in range(N):
        city_id = model.evaluate(S[d]).as_long()
        itinerary.append({"day": d + 1, "city": id_to_city[city_id]})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    solve_itinerary()
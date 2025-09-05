import json
from z3 import *

def main():
    # Define cities and required stays (in days, counting travel-day overlaps)
    cities = [
        "Reykjavik",
        "Riga",
        "Oslo",
        "Lyon",
        "Dubrovnik",
        "Madrid",
        "Warsaw",
        "London",
    ]
    city_idx = {c: i for i, c in enumerate(cities)}
    idx_city = {i: c for c, i in city_idx.items()}

    required_days = {
        "Reykjavik": 4,
        "Riga": 2,
        "Oslo": 3,
        "Lyon": 5,
        "Dubrovnik": 2,
        "Madrid": 2,
        "Warsaw": 4,
        "London": 3,
    }

    total_days = 18

    # Direct flights: build directed adjacency
    directed_edges = set()

    def add_undirected(a, b):
        directed_edges.add((city_idx[a], city_idx[b]))
        directed_edges.add((city_idx[b], city_idx[a]))

    def add_directed(a, b):
        directed_edges.add((city_idx[a], city_idx[b]))

    # Given direct flights
    add_undirected("Warsaw", "Reykjavik")
    add_undirected("Oslo", "Madrid")
    add_undirected("Warsaw", "Riga")
    add_undirected("Lyon", "London")
    add_undirected("Madrid", "London")
    add_undirected("Warsaw", "London")
    add_directed("Reykjavik", "Madrid")  # directed as specified
    add_undirected("Warsaw", "Oslo")
    add_undirected("Oslo", "Dubrovnik")
    add_undirected("Oslo", "Reykjavik")
    add_undirected("Riga", "Oslo")
    add_undirected("Oslo", "Lyon")
    add_undirected("Oslo", "London")
    add_undirected("London", "Reykjavik")
    add_undirected("Warsaw", "Madrid")
    add_undirected("Madrid", "Lyon")
    add_undirected("Dubrovnik", "Madrid")

    # Z3 model
    s = Solver()

    # Variables: location at end of each day (1..total_days)
    Loc = [None] + [Int(f"Loc_{d}") for d in range(1, total_days + 1)]
    for d in range(1, total_days + 1):
        s.add(And(Loc[d] >= 0, Loc[d] < len(cities)))  # domain restriction

    # Flight/change days
    # Make array long enough to index up to total_days
    change_flags = [None] + [Bool(f"Change_{d}") for d in range(1, total_days + 1)]
    for d in range(2, total_days + 1):
        s.add(change_flags[d] == (Loc[d] != Loc[d - 1]))

    # Exactly 7 flights (since total city-day requirements sum to 25 and total days are 18)
    s.add(Sum([If(change_flags[d], 1, 0) for d in range(2, total_days + 1)]) == 7)

    # Direct flight constraint on change days
    for d in range(2, total_days + 1):
        if directed_edges:
            allowed_pairs = Or(*[And(Loc[d - 1] == a, Loc[d] == b) for (a, b) in directed_edges])
        else:
            allowed_pairs = BoolVal(False)
        s.add(Or(Not(change_flags[d]), allowed_pairs))

    # Helper: presence predicate (in city c on day d)
    def in_city_expr(c_int, d):
        if d == 1:
            return Loc[d] == c_int
        else:
            return Or(
                Loc[d] == c_int,                              # end the day in city c
                And(Loc[d - 1] == c_int, change_flags[d])     # departed from c on day d
            )

    # City duration constraints
    for cname, req in required_days.items():
        c = city_idx[cname]
        s.add(Sum([If(in_city_expr(c, d), 1, 0) for d in range(1, total_days + 1)]) == req)

    # Meeting in Riga between day 4 and day 5 (on either day)
    riga = city_idx["Riga"]
    s.add(Or(in_city_expr(riga, 4), in_city_expr(riga, 5)))

    # Wedding in Dubrovnik between day 7 and day 8 (on either day)
    dubrovnik = city_idx["Dubrovnik"]
    s.add(Or(in_city_expr(dubrovnik, 7), in_city_expr(dubrovnik, 8)))

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = s.model()
    loc_values = [None] + [m.evaluate(Loc[d]).as_long() for d in range(1, total_days + 1)]

    # Build itinerary as contiguous segments by city (based on end-of-day Loc)
    itinerary = []
    start_day = 1
    current_city = loc_values[1]
    for d in range(2, total_days + 1):
        if loc_values[d] != current_city:
            itinerary.append({
                "day_range": f"Day {start_day}-{d-1}",
                "place": idx_city[current_city]
            })
            start_day = d
            current_city = loc_values[d]
    itinerary.append({
        "day_range": f"Day {start_day}-{total_days}",
        "place": idx_city[current_city]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
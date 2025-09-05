import json
from z3 import *

def solve_itinerary():
    # Cities and indices
    cities = ["Hamburg", "Zurich", "Helsinki", "Bucharest", "Split"]
    idx = {c: i for i, c in enumerate(cities)}

    # Required stay durations per city
    required_durations = {
        "Hamburg": 2,
        "Zurich": 3,
        "Helsinki": 2,
        "Bucharest": 2,
        "Split": 7
    }

    # Undirected direct flight edges
    direct_edges = [
        ("Zurich", "Helsinki"),
        ("Hamburg", "Bucharest"),
        ("Helsinki", "Hamburg"),
        ("Zurich", "Hamburg"),
        ("Zurich", "Bucharest"),
        ("Zurich", "Split"),
        ("Helsinki", "Split"),
        ("Split", "Hamburg"),
    ]
    allowed_pairs = set()
    for a, b in direct_edges:
        allowed_pairs.add((idx[a], idx[b]))
        allowed_pairs.add((idx[b], idx[a]))

    # Z3 variables
    # order[i] = city index occupying block i (i=0..4)
    order = [Int(f"order_{i}") for i in range(5)]
    # Change days t1 < t2 < t3 < t4 within 1..12
    t1, t2, t3, t4 = Ints("t1 t2 t3 t4")

    s = Solver()

    # Bounds and distinctness for order
    for i in range(5):
        s.add(order[i] >= 0, order[i] < 5)
    s.add(Distinct(order))

    # Bounds for change days
    s.add(t1 >= 1, t4 <= 12, t1 < t2, t2 < t3, t3 < t4)

    # Define block durations (inclusive with overlap on flight days)
    dur0 = t1
    dur1 = t2 - t1 + 1
    dur2 = t3 - t2 + 1
    dur3 = t4 - t3 + 1
    dur4 = 13 - t4
    durs = [dur0, dur1, dur2, dur3, dur4]

    # Each block's duration must match the required duration of its assigned city
    # Enforce piecewise equalities based on which city is assigned to each block
    for i in range(5):
        # Build constraints that dur[i] equals the required duration of the selected city
        conds = []
        for c in cities:
            conds.append(And(order[i] == idx[c], durs[i] == required_durations[c]))
        s.add(Or(conds))

    # Direct flights only between consecutive blocks
    for i in range(4):
        s.add(Or([And(order[i] == a, order[i+1] == b) for (a, b) in allowed_pairs]))

    # Define block start and end days (inclusive)
    start = [None]*5
    end = [None]*5
    start[0] = IntVal(1)
    end[0] = t1
    start[1] = t1
    end[1] = t2
    start[2] = t2
    end[2] = t3
    start[3] = t3
    end[3] = t4
    start[4] = t4
    end[4] = IntVal(12)

    # Conference in Split on days 4 and 10
    split_idx = idx["Split"]
    def in_block_day(city_idx, day):
        return Or([And(order[i] == city_idx, start[i] <= day, day <= end[i]) for i in range(5)])
    s.add(in_block_day(split_idx, IntVal(4)))
    s.add(in_block_day(split_idx, IntVal(10)))

    # Wedding in Zurich between day 1 and day 3
    zurich_idx = idx["Zurich"]
    s.add(Or([in_block_day(zurich_idx, IntVal(d)) for d in [1, 2, 3]]))

    # Solve
    if s.check() != sat:
        return {"itinerary": []}

    m = s.model()

    # Extract values
    order_vals = [m.evaluate(order[i]).as_long() for i in range(5)]
    t1v = m.evaluate(t1).as_long()
    t2v = m.evaluate(t2).as_long()
    t3v = m.evaluate(t3).as_long()
    t4v = m.evaluate(t4).as_long()

    starts = [1, t1v, t2v, t3v, t4v]
    ends = [t1v, t2v, t3v, t4v, 12]

    itinerary = []
    for i in range(5):
        place = cities[order_vals[i]]
        day_range = f"Day {starts[i]}-{ends[i]}"
        itinerary.append({"day_range": day_range, "place": place})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result))
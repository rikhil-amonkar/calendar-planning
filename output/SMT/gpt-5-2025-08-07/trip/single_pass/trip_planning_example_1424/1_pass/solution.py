import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = [
        "Warsaw",
        "Porto",
        "Naples",
        "Brussels",
        "Split",
        "Reykjavik",
        "Amsterdam",
        "Lyon",
        "Helsinki",
        "Valencia",
    ]
    idx = {c: i for i, c in enumerate(cities)}

    # Required total presence (days counted per city, including flight overlap)
    required = {
        "Warsaw": 3,
        "Porto": 5,
        "Naples": 4,
        "Brussels": 3,
        "Split": 3,
        "Reykjavik": 5,
        "Amsterdam": 4,
        "Lyon": 3,
        "Helsinki": 4,
        "Valencia": 2,
    }

    # Direct flights (undirected)
    direct_pairs = [
        ("Amsterdam", "Warsaw"),
        ("Helsinki", "Brussels"),
        ("Helsinki", "Warsaw"),
        ("Reykjavik", "Brussels"),
        ("Amsterdam", "Lyon"),
        ("Amsterdam", "Naples"),
        ("Amsterdam", "Reykjavik"),
        ("Naples", "Valencia"),
        ("Porto", "Brussels"),
        ("Amsterdam", "Split"),
        ("Lyon", "Split"),
        ("Warsaw", "Split"),
        ("Porto", "Amsterdam"),
        ("Helsinki", "Split"),
        ("Brussels", "Lyon"),
        ("Porto", "Lyon"),
        ("Reykjavik", "Warsaw"),
        ("Brussels", "Valencia"),
        ("Valencia", "Lyon"),
        ("Porto", "Warsaw"),
        ("Warsaw", "Valencia"),
        ("Amsterdam", "Helsinki"),
        ("Porto", "Valencia"),
        ("Warsaw", "Brussels"),
        ("Warsaw", "Naples"),
        ("Naples", "Split"),
        ("Helsinki", "Naples"),
        ("Helsinki", "Reykjavik"),
        ("Amsterdam", "Valencia"),
        ("Naples", "Brussels"),
    ]
    # Build allowed ordered transitions (i->j)
    allowed = set()
    for a, b in direct_pairs:
        allowed.add((idx[a], idx[b]))
        allowed.add((idx[b], idx[a]))

    days = 27
    # Variables: city assigned each day (0..9)
    City = [Int(f"City_{d}") for d in range(1, days + 1)]

    s = Solver()

    # Domain constraints
    for d in range(days):
        s.add(And(City[d] >= 0, City[d] < len(cities)))

    # Transition constraints: if city changes, it must be a direct flight
    for d in range(1, days):
        prev = City[d - 1]
        cur = City[d]
        # If prev != cur, (prev, cur) must be in allowed
        allowed_or = Or(*[And(prev == i, cur == j) for (i, j) in allowed]) if allowed else False
        s.add(Or(prev == cur, allowed_or))

    # Helper: presence predicate for a city c on a given day d (1-based day index)
    def presence_expr(c_idx, d1_based):
        d = d1_based - 1  # 0-based index for City array
        if d1_based == 1:
            return City[d] == c_idx
        prev = City[d - 1]
        cur = City[d]
        return Or(cur == c_idx, And(prev == c_idx, cur != prev))

    # City presence = assigned days + departure days
    # assigned days: count of days where City[d] == c
    # departure days: count of days t in 2..27 where City[t-1] == c and City[t] != City[t-1]
    for name, t_required in required.items():
        c = idx[name]
        assigned_count = Sum([If(City[d] == c, 1, 0) for d in range(days)])
        depart_count = Sum([
            If(And(City[d - 1] == c, City[d] != City[d - 1]), 1, 0)
            for d in range(1, days)
        ])
        s.add(assigned_count + depart_count == t_required)

    # Event/window constraints (presence on each day in the window)
    # Porto workshop: days 1..5
    for d in range(1, 6):
        s.add(presence_expr(idx["Porto"], d))
    # Amsterdam relatives: days 5..8
    for d in range(5, 9):
        s.add(presence_expr(idx["Amsterdam"], d))
    # Helsinki wedding: days 8..11
    for d in range(8, 12):
        s.add(presence_expr(idx["Helsinki"], d))
    # Naples conference: days 17..20
    for d in range(17, 21):
        s.add(presence_expr(idx["Naples"], d))
    # Brussels show: days 20..22
    for d in range(20, 23):
        s.add(presence_expr(idx["Brussels"], d))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found")

    m = s.model()
    itinerary = []
    for d in range(days):
        c_index = m.eval(City[d]).as_long()
        itinerary.append({"day": d + 1, "city": cities[c_index]})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_itinerary()
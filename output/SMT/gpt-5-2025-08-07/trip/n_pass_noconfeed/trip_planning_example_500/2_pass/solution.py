import json
from z3 import *

def main():
    # City enumeration
    HAMBURG, MUNICH, MANCHESTER, LYON, SPLIT = 0, 1, 2, 3, 4
    city_names = {HAMBURG: "Hamburg", MUNICH: "Munich", MANCHESTER: "Manchester", LYON: "Lyon", SPLIT: "Split"}

    # Required in-city day counts (counting flight-day overlap as presence in both cities)
    required_days = {
        HAMBURG: 7,
        MUNICH: 6,
        MANCHESTER: 2,
        LYON: 2,
        SPLIT: 7
    }

    # Allowed directed edges (direct flights)
    allowed_pairs = set()
    def add_undirected(a, b):
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))
    # Given connections
    add_undirected(SPLIT, MUNICH)
    add_undirected(MUNICH, MANCHESTER)
    add_undirected(HAMBURG, MANCHESTER)
    add_undirected(HAMBURG, MUNICH)
    add_undirected(SPLIT, LYON)
    add_undirected(LYON, MUNICH)
    add_undirected(HAMBURG, SPLIT)
    # Directional: from Manchester to Split
    allowed_pairs.add((MANCHESTER, SPLIT))

    days = 20
    s = Solver()

    # Variables: city assigned for each day (1..20)
    city = [Int(f"city_{d}") for d in range(1, days + 1)]
    for d in range(days):
        s.add(And(city[d] >= 0, city[d] <= 4))

    # Flight boolean for day d (2..20): True if city change from d-1 to d
    # Align indices so that flight[d] exists for all d in 0..days and is used only for d>=2
    flight = [None] * (days + 1)
    for d in range(2, days + 1):
        flight[d] = Bool(f"flight_{d}")
        s.add(flight[d] == (city[d - 2] != city[d - 1]))
        # If a flight occurs, it must be along an allowed direct edge
        allowed = Or(*[And(city[d - 2] == a, city[d - 1] == b) for (a, b) in allowed_pairs])
        s.add(Implies(flight[d], allowed))

    # In-city predicate: present in city c on day d (counts flight-day overlap)
    def in_city_expr(c, d):
        if d == 1:
            return city[0] == c
        else:
            return Or(city[d - 1] == c, And(flight[d], city[d - 2] == c))

    # Duration constraints: exact days in each city
    for c, req in required_days.items():
        s.add(Sum([If(in_city_expr(c, d), 1, 0) for d in range(1, days + 1)]) == req)

    # Show in Lyon on day 13 and day 14 (presence, possibly via flight overlap)
    s.add(in_city_expr(LYON, 13))
    s.add(in_city_expr(LYON, 14))

    # Visit relatives in Manchester on days 19 and 20
    s.add(city[18] == MANCHESTER)  # Assigned to Manchester on day 19
    s.add(city[19] == MANCHESTER)  # Assigned to Manchester on day 20
    s.add(in_city_expr(MANCHESTER, 19))
    s.add(in_city_expr(MANCHESTER, 20))

    # Total number of flights equals total extra counted city-days = 24 - 20 = 4
    s.add(Sum([If(flight[d], 1, 0) for d in range(2, days + 1)]) == 4)

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": []}))
        return
    m = s.model()

    assigned = [m.evaluate(city[d]).as_long() for d in range(days)]

    # Compress into contiguous ranges by assigned city
    itinerary = []
    start = 1
    current_city = assigned[0]
    for d in range(2, days + 1):
        if assigned[d - 1] != current_city:
            itinerary.append({
                "day_range": f"Day {start}-{d-1}",
                "place": city_names[current_city]
            })
            start = d
            current_city = assigned[d - 1]
    # Append last range
    itinerary.append({
        "day_range": f"Day {start}-{days}",
        "place": city_names[current_city]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
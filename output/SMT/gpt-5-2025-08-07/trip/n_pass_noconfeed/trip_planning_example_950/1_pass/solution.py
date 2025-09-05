import json
from z3 import *

def solve_itinerary():
    # Cities and indices
    cities = ["Rome", "Mykonos", "Nice", "Riga", "Bucharest", "Munich", "Krakow"]
    city_idx = {c: i for i, c in enumerate(ccities := cities)}
    n_cities = len(cities)

    total_days = 17
    days = list(range(total_days))  # 0-based for internal use; represents Day 1..17

    # Stay durations (counting flight days for both cities)
    required_days = {
        "Rome": 4,
        "Mykonos": 3,
        "Nice": 3,
        "Riga": 3,
        "Bucharest": 4,
        "Munich": 4,
        "Krakow": 2,
    }

    # Direct flight edges
    undirected_pairs = [
        ("Nice", "Riga"),
        ("Bucharest", "Munich"),
        ("Mykonos", "Munich"),
        ("Riga", "Bucharest"),
        ("Rome", "Nice"),
        ("Rome", "Munich"),
        ("Mykonos", "Nice"),
        ("Rome", "Mykonos"),
        ("Munich", "Krakow"),
        ("Rome", "Bucharest"),
        ("Nice", "Munich"),
    ]
    directed_pairs = [
        ("Riga", "Munich"),
        ("Rome", "Riga"),
    ]

    # Build allowed directed edges as index pairs
    allowed_edges = set()
    for a, b in undirected_pairs:
        allowed_edges.add((city_idx[a], city_idx[b]))
        allowed_edges.add((city_idx[b], city_idx[a]))
    for a, b in directed_pairs:
        allowed_edges.add((city_idx[a], city_idx[b]))

    def allowed_expr(u, v):
        return Or([And(u == a, v == b) for (a, b) in allowed_edges]) if allowed_edges else False

    s = Solver()

    # Variables
    start_city = Int("start_city")
    s.add(start_city >= 0, start_city < n_cities)

    main_city = [Int(f"main_{d+1}") for d in days]   # city you end Day d+1 in
    prev_city = [Int(f"prev_{d+1}") for d in days]   # city you begin Day d+1 in
    flight = [Bool(f"flight_{d+1}") for d in days]   # whether a flight occurs on Day d+1

    for d in days:
        s.add(main_city[d] >= 0, main_city[d] < n_cities)
        s.add(prev_city[d] >= 0, prev_city[d] < n_cities)

    # Link prev_city and main_city over days
    s.add(prev_city[0] == start_city)  # Day 1 starts at start_city
    for d in range(1, total_days):
        s.add(prev_city[d] == main_city[d-1])  # Day d+1 starts where Day d ended

    # Flight logic and direct-flight constraint
    for d in days:
        # flight[d] iff prev_city[d] != main_city[d]
        s.add(Or(And(flight[d], prev_city[d] != main_city[d]),
                 And(Not(flight[d]), prev_city[d] == main_city[d])))
        # If flight, must be a direct flight
        s.add(Implies(flight[d], allowed_expr(prev_city[d], main_city[d])))

    # Presence per city per day (1 if present in prev or main on that day, else 0)
    present = {}
    for c in range(n_cities):
        present[c] = []
        for d in days:
            present_cd = Int(f"present_{c}_{d+1}")
            s.add(present_cd >= 0, present_cd <= 1)
            s.add(If(Or(prev_city[d] == c, main_city[d] == c), present_cd == 1, present_cd == 0))
            present[c].append(present_cd)

    # Durations: sum of presence per city equals the required days
    for cname, req in required_days.items():
        c = city_idx[cname]
        s.add(Sum(present[c]) == req)

    # Total flights equals total overlap needed = sum(required_days) - total_days
    total_required = sum(required_days.values())
    required_flights = total_required - total_days
    s.add(Sum([If(flight[d], 1, 0) for d in days]) == required_flights)

    # Specific day constraints (1-based days in description)
    # Day 1 and Day 4 must include Rome
    s.add(present[city_idx["Rome"]][0] == 1)  # Day 1
    s.add(present[city_idx["Rome"]][3] == 1)  # Day 4

    # Mykonos on days 4,5,6
    s.add(present[city_idx["Mykonos"]][3] == 1)  # Day 4
    s.add(present[city_idx["Mykonos"]][4] == 1)  # Day 5
    s.add(present[city_idx["Mykonos"]][5] == 1)  # Day 6

    # Krakow on days 16 and 17
    s.add(present[city_idx["Krakow"]][15] == 1)  # Day 16
    s.add(present[city_idx["Krakow"]][16] == 1)  # Day 17

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    m = s.model()

    # Extract values
    start = m[start_city].as_long()
    main_vals = [m[mc].as_long() for mc in main_city]
    prev_vals = [m[pc].as_long() for pc in prev_city]
    flight_days = [i+1 for i in days if is_true(m[flight[i]])]

    # Build route sequence: start city followed by the destination city of each flight day
    route = [start] + [main_vals[d-1] for d in flight_days]

    # Construct itinerary as overlapping segments:
    # Segment i spans from (start_day) to (flight_day_i) and is for route[i]
    # Next segment starts at flight_day_i to next flight day, etc. Last ends at Day 17
    itinerary = []
    current_start_day = 1
    for i, fd in enumerate(flight_days):
        itinerary.append({
            "day_range": f"Day {current_start_day}-{fd}",
            "place": cities[route[i]]
        })
        current_start_day = fd
    # Final segment
    itinerary.append({
        "day_range": f"Day {current_start_day}-{total_days}",
        "place": cities[route[-1]]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    solve_itinerary()
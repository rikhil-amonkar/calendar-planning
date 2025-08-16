from z3 import *
import json

def solve_itinerary():
    # Constants
    N_DAYS = 15
    cities = ["Dublin", "Helsinki", "Riga", "Reykjavik", "Vienna", "Tallinn"]
    city_index = {name: i for i, name in enumerate(cities)}

    # Required total "day counts" per city (including flight days counted twice)
    required = {
        "Dublin": 5,
        "Helsinki": 3,
        "Riga": 3,
        "Reykjavik": 2,
        "Vienna": 2,
        "Tallinn": 5
    }

    # Build allowed directed flight pairs
    # "A and B" -> add both (A,B) and (B,A)
    # "from A to B" -> add only (A,B)
    undirected_pairs = [
        ("Helsinki", "Riga"),
        ("Vienna", "Helsinki"),
        ("Riga", "Dublin"),
        ("Vienna", "Riga"),
        ("Reykjavik", "Vienna"),
        ("Helsinki", "Dublin"),
        ("Tallinn", "Dublin"),
        ("Reykjavik", "Helsinki"),
        ("Reykjavik", "Dublin"),
        ("Helsinki", "Tallinn"),
        ("Vienna", "Dublin"),
    ]
    directed_pairs = [
        ("Riga", "Tallinn"),
    ]

    allowed = set()
    for a, b in undirected_pairs:
        allowed.add((city_index[a], city_index[b]))
        allowed.add((city_index[b], city_index[a]))
    for a, b in directed_pairs:
        allowed.add((city_index[a], city_index[b]))

    # Decision variables: place[d] = city index at end of day d (1..N_DAYS)
    place = [Int(f"place_{d}") for d in range(1, N_DAYS + 1)]

    s = Solver()

    # Domain constraints
    for d in range(N_DAYS):
        s.add(And(place[d] >= 0, place[d] < len(cities)))

    # Direct flight or stay constraints (for day >= 2)
    for d in range(1, N_DAYS):
        prev = place[d - 1]
        curr = place[d]
        stay = (curr == prev)
        # Or there is a direct flight from prev to curr
        flight_terms = []
        for (u, v) in allowed:
            flight_terms.append(And(prev == u, curr == v))
        s.add(Or(stay, Or(flight_terms)))

    # Presence indicators inc[c][d]: whether city c is "counted" on day d
    # Day d counts for place[d] always; if d>1 and place[d-1]!=place[d], day d also counts for place[d-1]
    inc = {}
    for c in range(len(cities)):
        inc[c] = [Bool(f"inc_{c}_{d}") for d in range(1, N_DAYS + 1)]

    for d in range(N_DAYS):
        curr = place[d]
        if d == 0:
            for c in range(len(cities)):
                s.add(inc[c][d] == (curr == c))
        else:
            prev = place[d - 1]
            for c in range(len(cities)):
                s.add(inc[c][d] ==
                      Or(curr == c, And(prev == c, curr != prev)))

    # City day-count requirements
    for name, req in required.items():
        c = city_index[name]
        s.add(Sum([If(inc[c][d], 1, 0) for d in range(N_DAYS)]) == req)

    # Event constraints

    # Vienna show from day 2 to day 3 => must be "in Vienna" on both days 2 and 3
    vienna = city_index["Vienna"]
    s.add(inc[vienna][1] == True)  # day index 2 (0-based -> 1)
    s.add(inc[vienna][2] == True)  # day index 3 (0-based -> 2)

    # Meet friends in Helsinki between days 3 and 5: at least one of these days is in Helsinki
    helsinki = city_index["Helsinki"]
    s.add(Or(inc[helsinki][2], inc[helsinki][3], inc[helsinki][4]))  # days 3,4,5

    # Attend a wedding in Tallinn between day 7 and day 11: at least one day in this window in Tallinn
    tallinn = city_index["Tallinn"]
    s.add(Or([inc[tallinn][d] for d in range(6, 11)]))  # days 7..11

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = s.model()
    itinerary = []
    for d in range(N_DAYS):
        city_idx = m[place[d]].as_long()
        itinerary.append({"day": d + 1, "city": cities[city_idx]})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    solve_itinerary()
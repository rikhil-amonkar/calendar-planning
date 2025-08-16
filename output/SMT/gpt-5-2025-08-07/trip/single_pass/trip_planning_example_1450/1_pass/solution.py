import json
from z3 import *

def solve_itinerary():
    # Days
    D = 32
    days = list(range(1, D + 1))

    # Cities and indices
    cities = [
        "Stockholm",  # 0
        "Hamburg",    # 1
        "Florence",   # 2
        "Istanbul",   # 3
        "Oslo",       # 4
        "Vilnius",    # 5
        "Santorini",  # 6
        "Munich",     # 7
        "Frankfurt",  # 8
        "Krakow"      # 9
    ]
    idx = {c: i for i, c in enumerate(cities)}

    # Required total "presence days" per city (including flight-day double counts)
    required_days = {
        idx["Stockholm"]: 3,
        idx["Hamburg"]: 5,
        idx["Florence"]: 2,
        idx["Istanbul"]: 5,
        idx["Oslo"]: 5,
        idx["Vilnius"]: 5,
        idx["Santorini"]: 2,
        idx["Munich"]: 5,
        idx["Frankfurt"]: 4,
        idx["Krakow"]: 5
    }

    # Directed adjacency for flights between different cities
    # Note: staying in the same city is always allowed; this only controls when city changes.
    allowed = set()

    def add_edge(a, b, bidir=False):
        allowed.add((idx[a], idx[b]))
        if bidir:
            allowed.add((idx[b], idx[a]))

    # Parse given connections
    add_edge("Oslo", "Stockholm", bidir=True)
    add_edge("Krakow", "Frankfurt", bidir=True)
    add_edge("Krakow", "Istanbul", bidir=True)
    add_edge("Munich", "Stockholm", bidir=True)
    add_edge("Hamburg", "Stockholm", bidir=True)
    add_edge("Krakow", "Vilnius", bidir=False)  # from Krakow to Vilnius
    add_edge("Oslo", "Istanbul", bidir=True)
    add_edge("Istanbul", "Stockholm", bidir=True)
    add_edge("Oslo", "Krakow", bidir=True)
    add_edge("Vilnius", "Istanbul", bidir=True)
    add_edge("Oslo", "Vilnius", bidir=True)
    add_edge("Frankfurt", "Istanbul", bidir=True)
    add_edge("Oslo", "Frankfurt", bidir=True)
    add_edge("Munich", "Hamburg", bidir=True)
    add_edge("Munich", "Istanbul", bidir=True)
    add_edge("Oslo", "Munich", bidir=True)
    add_edge("Frankfurt", "Florence", bidir=True)
    add_edge("Oslo", "Hamburg", bidir=True)
    add_edge("Vilnius", "Frankfurt", bidir=True)
    add_edge("Florence", "Munich", bidir=False)  # from Florence to Munich
    add_edge("Krakow", "Munich", bidir=True)
    add_edge("Hamburg", "Istanbul", bidir=True)
    add_edge("Frankfurt", "Stockholm", bidir=True)
    add_edge("Stockholm", "Santorini", bidir=False)  # from Stockholm to Santorini
    add_edge("Frankfurt", "Munich", bidir=True)
    add_edge("Santorini", "Oslo", bidir=False)  # from Santorini to Oslo
    add_edge("Krakow", "Stockholm", bidir=True)
    add_edge("Vilnius", "Munich", bidir=False)  # from Vilnius to Munich
    add_edge("Frankfurt", "Hamburg", bidir=True)

    # Variables: city_at_day[d] is the city index on day d (1-based for readability)
    city_at_day = [Int(f"city_{d}") for d in days]

    s = Solver()

    # Domain constraints
    for v in city_at_day:
        s.add(And(v >= 0, v < len(cities)))

    # Flight adjacency constraints for day transitions:
    # If city changes from day d-1 to d, the pair must be in allowed set.
    for d in days:
        if d == 1:
            continue
        prev = city_at_day[d - 2]
        cur = city_at_day[d - 1]
        # Either staying, or use an allowed directed edge
        allowed_disj = Or([And(prev == a, cur == b) for (a, b) in allowed]) if allowed else False
        s.add(Or(cur == prev, allowed_disj))

    # Helper: presence predicate for city c on day d (counts departure day and arrival day)
    def present(c_idx, d):
        if d == 1:
            return city_at_day[0] == c_idx
        prev = city_at_day[d - 2]
        cur = city_at_day[d - 1]
        return Or(cur == c_idx, And(prev == c_idx, cur != prev))

    # Exact total "presence days" per city
    for c_idx, req in required_days.items():
        base = Sum([If(city_at_day[d - 1] == c_idx, 1, 0) for d in days])
        departures = Sum([If(And(city_at_day[d - 2] == c_idx, city_at_day[d - 1] != city_at_day[d - 2]), 1, 0) for d in days if d > 1])
        s.add(base + departures == req)

    # Total flights equals 9 (since sum of required days = 41 = 32 + flights)
    flights = Sum([If(city_at_day[d - 1] != city_at_day[d - 2], 1, 0) for d in days if d > 1])
    s.add(flights == 9)

    # Workshop in Krakow between day 5 and 9: be present at least one day in that window
    krk = idx["Krakow"]
    s.add(Or([present(krk, d) for d in range(5, 10)]))

    # Annual show in Istanbul between day 25 and 29: be present at least one day in that window
    ist = idx["Istanbul"]
    s.add(Or([present(ist, d) for d in range(25, 30)]))

    # Solve
    if s.check() != sat:
        # If unsat, return empty itinerary
        return {"itinerary": []}

    m = s.model()
    itinerary = []
    for d in days:
        c = m[city_at_day[d - 1]].as_long()
        itinerary.append({"day": d, "place": cities[c]})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))
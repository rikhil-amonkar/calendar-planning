import json
from z3 import *

def solve_itinerary():
    # Cities and indices
    cities = [
        "Oslo",        # 0
        "Stockholm",   # 1
        "Krakow",      # 2
        "Frankfurt",   # 3
        "Istanbul",    # 4
        "Munich",      # 5
        "Hamburg",     # 6
        "Florence",    # 7
        "Vilnius",     # 8
        "Santorini"    # 9
    ]
    idx = {c:i for i,c in enumerate(cities)}

    # Required exact days in each city
    required_days = {
        "Stockholm": 3,
        "Hamburg": 5,
        "Florence": 2,
        "Istanbul": 5,
        "Oslo": 5,
        "Vilnius": 5,
        "Santorini": 2,
        "Munich": 5,
        "Frankfurt": 4,
        "Krakow": 5,
    }

    # Build directed adjacency based on provided direct flights
    E = set()
    def add_bidirectional(a,b):
        E.add((idx[a], idx[b]))
        E.add((idx[b], idx[a]))
    def add_direct(a,b):
        E.add((idx[a], idx[b]))

    # Given direct flights list
    add_bidirectional("Oslo", "Stockholm")
    add_bidirectional("Krakow", "Frankfurt")
    add_bidirectional("Krakow", "Istanbul")
    add_bidirectional("Munich", "Stockholm")
    add_bidirectional("Hamburg", "Stockholm")
    add_direct("Krakow", "Vilnius")
    add_bidirectional("Oslo", "Istanbul")
    add_bidirectional("Istanbul", "Stockholm")
    add_bidirectional("Oslo", "Krakow")
    add_bidirectional("Vilnius", "Istanbul")
    add_bidirectional("Oslo", "Vilnius")
    add_bidirectional("Frankfurt", "Istanbul")
    add_bidirectional("Oslo", "Frankfurt")
    add_bidirectional("Munich", "Hamburg")
    add_bidirectional("Munich", "Istanbul")
    add_bidirectional("Oslo", "Munich")
    add_bidirectional("Frankfurt", "Florence")
    add_bidirectional("Oslo", "Hamburg")
    add_bidirectional("Vilnius", "Frankfurt")
    add_direct("Florence", "Munich")
    add_bidirectional("Krakow", "Munich")
    add_bidirectional("Hamburg", "Istanbul")
    add_bidirectional("Frankfurt", "Stockholm")
    add_direct("Stockholm", "Santorini")
    add_bidirectional("Frankfurt", "Munich")
    add_direct("Santorini", "Oslo")
    add_bidirectional("Krakow", "Stockholm")
    add_direct("Vilnius", "Munich")
    add_bidirectional("Frankfurt", "Hamburg")

    days = 32
    # Variables: location per day (1..32)
    loc = [Int(f"loc_{d}") for d in range(1, days+1)]

    s = Optimize()

    # Domain constraints
    for v in loc:
        s.add(And(v >= 0, v < len(cities)))

    # Flight constraints: if change city between day d-1 and d, flight must be direct
    def direct_edge(a, b):
        # returns z3 Bool: (a,b) in E
        return Or([And(a == i, b == j) for (i,j) in E]) if E else False

    for d in range(1, days):  # 0-based indexing for Python; day d corresponds to day number d+1
        prev = loc[d-1]
        curr = loc[d]
        s.add(Or(curr == prev, direct_edge(prev, curr)))

    # Helper: in_city on day d for city c, considering flight-day overlap
    # in_city[d][c] is true if on day d the traveler is in city c (possibly due to flight overlap)
    in_city = {}
    for c in range(len(cities)):
        in_city[c] = []
        for d in range(1, days+1):
            if d == 1:
                in_c = (loc[d-1] == c)
            else:
                # in city c on day d if:
                # - base location is c on day d, OR
                # - there is a transition into day d and previous day location was c
                in_c = Or(loc[d-1] == c, And(loc[d-2] == c, loc[d-1] != loc[d-2]))
            in_city[c].append(in_c)

    # Exact days per city (sum of in_city per day equals required)
    for cname, req in required_days.items():
        c = idx[cname]
        s.add(Sum([If(in_city[c][d-1], 1, 0) for d in range(1, days+1)]) == req)

    # Must be in Istanbul on days 25..29 inclusive (show)
    IST = idx["Istanbul"]
    for d in range(25, 30):
        s.add(in_city[IST][d-1])

    # Krakow workshop: must be in Krakow on at least one day between 5 and 9 inclusive
    KRK = idx["Krakow"]
    s.add(Or([in_city[KRK][d-1] for d in range(5, 10)]))

    # Encourage a simple path visiting each city once: number of transitions must be 9 (10 cities -> 9 transitions)
    transitions = [If(loc[d] != loc[d-1], 1, 0) for d in range(1, days)]
    s.add(Sum(transitions) == 9)

    # Solve
    if s.check() != sat:
        return {"itinerary": []}

    m = s.model()
    loc_vals = [m.evaluate(loc[d]).as_long() for d in range(days)]

    # Build itinerary by contiguous base location runs
    itinerary = []
    start = 1
    current_city = loc_vals[0]
    for i in range(1, days):
        if loc_vals[i] != current_city:
            itinerary.append({
                "day_range": f"Day {start}-{i}",
                "place": cities[current_city]
            })
            start = i+1
            current_city = loc_vals[i]
    # Append last run
    itinerary.append({
        "day_range": f"Day {start}-{days}",
        "place": cities[current_city]
    })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False))
import json
from z3 import *

def main():
    # Cities
    cities = [
        "Stuttgart",
        "Istanbul",
        "Vilnius",
        "Seville",
        "Geneva",
        "Valencia",
        "Munich",
        "Reykjavik"
    ]
    city_idx = {name: i for i, name in enumerate(cities)}

    # Total days
    N = 25
    days = list(range(N))  # 0-based index for days; day 1 == index 0

    # Required stay durations per city (count including flight days as per rule)
    required_days = {
        "Stuttgart": 4,
        "Istanbul": 4,
        "Vilnius": 4,
        "Seville": 3,
        "Geneva": 5,
        "Valencia": 5,
        "Munich": 3,
        "Reykjavik": 4
    }

    # Special day presences (1-based days converted to 0-based indices)
    must_be_in = []
    # Reykjavik workshop between day 1 and day 4
    for d in range(1, 5):
        must_be_in.append((d - 1, "Reykjavik"))
    # Stuttgart conference on day 4 and day 7
    must_be_in.append((4 - 1, "Stuttgart"))
    must_be_in.append((7 - 1, "Stuttgart"))
    # Munich show day 13 to 15
    for d in range(13, 16):
        must_be_in.append((d - 1, "Munich"))
    # Istanbul relatives day 19 to 22
    for d in range(19, 23):
        must_be_in.append((d - 1, "Istanbul"))

    # Allowed direct flights (directed edges)
    allowed_pairs = set()
    def add_bidirectional(a, b):
        allowed_pairs.add((city_idx[a], city_idx[b]))
        allowed_pairs.add((city_idx[b], city_idx[a]))
    def add_unidirectional(a, b):
        allowed_pairs.add((city_idx[a], city_idx[b]))

    # Given connections:
    add_bidirectional("Geneva", "Istanbul")
    add_bidirectional("Reykjavik", "Munich")
    add_bidirectional("Stuttgart", "Valencia")
    add_unidirectional("Reykjavik", "Stuttgart")
    add_bidirectional("Stuttgart", "Istanbul")
    add_bidirectional("Munich", "Geneva")
    add_bidirectional("Istanbul", "Vilnius")
    add_bidirectional("Valencia", "Seville")
    add_bidirectional("Valencia", "Istanbul")
    add_unidirectional("Vilnius", "Munich")
    add_bidirectional("Seville", "Munich")
    add_bidirectional("Munich", "Istanbul")
    add_bidirectional("Valencia", "Geneva")
    add_bidirectional("Valencia", "Munich")

    # SMT variables
    city = [Int(f"city_{d+1}") for d in days]  # city per day (0..7)

    s = Solver()

    # Domain constraints
    for d in days:
        s.add(Or([city[d] == city_idx[name] for name in cities]))

    # Transition (flight) constraints: if city changes from day d to d+1, must be allowed direct flight
    for d in range(N - 1):
        s.add(Implies(city[d] != city[d + 1],
                      Or([And(city[d] == a, city[d + 1] == b) for (a, b) in allowed_pairs])))

    # Presence definition and duration constraints
    # presence[c][d] is a Bool indicating presence in city c on day d considering flight rule
    presence = {c: [Bool(f"present_{c}_{d+1}") for d in days] for c in cities}

    for d in days:
        for c in cities:
            c_idx = city_idx[c]
            # present on day d if:
            # 1) primary city that day is c, OR
            # 2) there is a flight on day d and destination (day d+1) is c
            if d < N - 1:
                s.add(presence[c][d] ==
                      Or(city[d] == c_idx,
                         And(city[d] != city[d + 1], city[d + 1] == c_idx)))
            else:
                # On last day, only primary city counts
                s.add(presence[c][d] == (city[d] == c_idx))

    # Duration constraints equal to required days
    for c in cities:
        s.add(Sum([If(presence[c][d], 1, 0) for d in days]) == required_days[c])

    # Special day presence constraints
    for (d, c) in must_be_in:
        s.add(presence[c][d])

    # Helpful anchoring constraints inferred from combined special-day requirements:
    # Day 4 must be Reykjavik->Stuttgart (to satisfy both Reykjavik and Stuttgart on day 4 and the directional constraint)
    # This is a logical consequence of the constraints but we add it to guide solving.
    s.add(city[3] == city_idx["Reykjavik"])
    s.add(city[4] == city_idx["Stuttgart"])

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    m = s.model()

    # Extract city per day
    day_cities = [None] * N
    for d in days:
        idx = m[city[d]].as_long()
        day_cities[d] = cities[idx]

    # Build itinerary segments by consecutive same primary city
    itinerary = []
    start = 0
    for d in range(1, N):
        if day_cities[d] != day_cities[d - 1]:
            itinerary.append({
                "day_range": f"Day {start + 1}-{d}",
                "place": day_cities[d - 1]
            })
            start = d
    itinerary.append({
        "day_range": f"Day {start + 1}-{N}",
        "place": day_cities[N - 1]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
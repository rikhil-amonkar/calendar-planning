import json
from z3 import *

def solve_itinerary():
    # Cities indices
    cities = [
        "Paris",       # 0
        "Warsaw",      # 1
        "Krakow",      # 2
        "Tallinn",     # 3
        "Riga",        # 4
        "Copenhagen",  # 5
        "Helsinki",    # 6
        "Oslo",        # 7
        "Santorini",   # 8
        "Lyon"         # 9
    ]
    name_to_idx = {name: i for i, name in enumerate(cities)}
    n_cities = len(cities)
    D = 25  # total days

    # Required total city-days (including travel-day double counting)
    required_days = {
        "Paris": 5,
        "Warsaw": 2,
        "Krakow": 2,
        "Tallinn": 2,
        "Riga": 2,
        "Copenhagen": 5,
        "Helsinki": 5,
        "Oslo": 5,
        "Santorini": 2,
        "Lyon": 4
    }
    req = [required_days[c] for c in cities]

    # Build directed adjacency for direct flights
    # By default, "A and B" means bidirectional; "from X to Y" means only X->Y.
    edges = set()
    def add_bidirectional(a, b):
        ai, bi = name_to_idx[a], name_to_idx[b]
        edges.add((ai, bi))
        edges.add((bi, ai))
    def add_direct(a, b):
        ai, bi = name_to_idx[a], name_to_idx[b]
        edges.add((ai, bi))

    add_bidirectional("Warsaw", "Riga")
    add_bidirectional("Warsaw", "Tallinn")
    add_bidirectional("Copenhagen", "Helsinki")
    add_bidirectional("Lyon", "Paris")
    add_bidirectional("Copenhagen", "Warsaw")
    add_bidirectional("Lyon", "Oslo")
    add_bidirectional("Paris", "Oslo")
    add_bidirectional("Paris", "Riga")
    add_bidirectional("Krakow", "Helsinki")
    add_bidirectional("Paris", "Tallinn")
    add_bidirectional("Oslo", "Riga")
    add_bidirectional("Krakow", "Warsaw")
    add_bidirectional("Paris", "Helsinki")
    add_bidirectional("Copenhagen", "Santorini")
    add_bidirectional("Helsinki", "Warsaw")
    add_bidirectional("Helsinki", "Riga")
    add_bidirectional("Copenhagen", "Krakow")
    add_bidirectional("Copenhagen", "Riga")
    add_bidirectional("Paris", "Krakow")
    add_bidirectional("Copenhagen", "Oslo")
    add_bidirectional("Oslo", "Tallinn")
    add_bidirectional("Oslo", "Helsinki")
    add_bidirectional("Copenhagen", "Tallinn")
    add_bidirectional("Oslo", "Krakow")
    add_direct("Riga", "Tallinn")       # one-way
    add_bidirectional("Helsinki", "Tallinn")
    add_bidirectional("Paris", "Copenhagen")
    add_bidirectional("Paris", "Warsaw")
    add_direct("Santorini", "Oslo")     # one-way
    add_bidirectional("Oslo", "Warsaw")

    # Z3 variables: start-city and end-city for each day
    s = [Int(f"s_{d}") for d in range(1, D + 1)]
    e = [Int(f"e_{d}") for d in range(1, D + 1)]

    opt = Optimize()

    # Domains
    for d in range(D):
        opt.add(And(s[d] >= 0, s[d] < n_cities))
        opt.add(And(e[d] >= 0, e[d] < n_cities))

    # Continuity: next day's start is previous day's end
    for d in range(D - 1):
        opt.add(s[d + 1] == e[d])

    # Allowed flights: either no flight (stay) or a direct edge s->e
    for d in range(D):
        opt.add(Or(e[d] == s[d], Or([And(s[d] == a, e[d] == b) for (a, b) in edges])))

    # Count flights (days where s != e)
    flights = [If(e[d] != s[d], 1, 0) for d in range(D)]
    total_flights = Sum(flights)
    opt.add(total_flights == 9)  # Since sum(city-days)=34 and D=25, flights must be 9

    # City-day counts: counts days as start city + inbound flight days (e != s and e == city)
    # cityDays[c] = Sum_d (s[d]==c) + Sum_d (e[d]==c and e[d]!=s[d])
    city_s_counts = [Sum([If(s[d] == c, 1, 0) for d in range(D)]) for c in range(n_cities)]
    city_inbound_counts = [Sum([If(And(e[d] == c, e[d] != s[d]), 1, 0) for d in range(D)]) for c in range(n_cities)]
    city_total_counts = [city_s_counts[c] + city_inbound_counts[c] for c in range(n_cities)]

    # Each city's required total days
    for c in range(n_cities):
        opt.add(city_total_counts[c] == req[c])

    # Each city entered at most once (ensures a single contiguous visit per city)
    for c in range(n_cities):
        opt.add(city_inbound_counts[c] <= 1)

    # Sum of inbound counts equals total flights
    opt.add(Sum(city_inbound_counts) == total_flights)

    # Special windows:
    # Paris: at least one day between day 4 and 8 inclusive
    Paris = name_to_idx["Paris"]
    opt.add(Sum([If(Or(s[d] == Paris, e[d] == Paris), 1, 0) for d in range(3, 8)]) >= 1)  # 0-based index adjust

    # Santorini: must be present on days 12 and 13
    Santorini = name_to_idx["Santorini"]
    for d in [11, 12]:  # days 12 and 13  -> 0-based indices 11,12
        opt.add(Or(s[d] == Santorini, e[d] == Santorini))

    # Krakow: must be present on days 17 and 18
    Krakow = name_to_idx["Krakow"]
    for d in [16, 17]:
        opt.add(Or(s[d] == Krakow, e[d] == Krakow))

    # Tallinn: total 2 days already enforced via required_days; specific window not required

    # Riga: must be present on days 23 and 24
    Riga = name_to_idx["Riga"]
    for d in [22, 23]:
        opt.add(Or(s[d] == Riga, e[d] == Riga))

    # Helsinki: at least one day between day 18 and 22 inclusive
    Helsinki = name_to_idx["Helsinki"]
    opt.add(Sum([If(Or(s[d] == Helsinki, e[d] == Helsinki), 1, 0) for d in range(17, 22)]) >= 1)

    # Optional: minimize number of flights on strict event days (prefer to avoid flying on those days if possible)
    event_days = set([11, 12, 16, 17, 22, 23])  # 0-based indices for 12,13,17,18,23,24
    minimize_event_flights = Sum([If(e[d] != s[d], 1, 0) for d in event_days])
    opt.minimize(minimize_event_flights)

    # Solve
    if opt.check() != sat:
        raise RuntimeError("No feasible itinerary found")

    m = opt.model()

    # Extract start cities per day
    s_vals = [m.evaluate(s[d]).as_long() for d in range(D)]
    e_vals = [m.evaluate(e[d]).as_long() for d in range(D)]

    # Build itinerary segments based on start-city blocks (contiguous same s)
    itinerary = []
    start_day = 1
    current_city = s_vals[0]
    for d in range(1, D):
        if s_vals[d] != current_city:
            itinerary.append({
                "day_range": f"Day {start_day}-{d}",
                "place": cities[current_city]
            })
            start_day = d + 1
            current_city = s_vals[d]
    # last segment
    itinerary.append({
        "day_range": f"Day {start_day}-{D}",
        "place": cities[current_city]
    })

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    solve_itinerary()
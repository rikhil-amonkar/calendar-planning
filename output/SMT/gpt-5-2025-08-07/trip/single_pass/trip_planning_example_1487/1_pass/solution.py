from z3 import *
import json

def solve_itinerary():
    # Define cities
    cities = [
        "Copenhagen",
        "Geneva",
        "Mykonos",
        "Naples",
        "Prague",
        "Dubrovnik",
        "Athens",
        "Santorini",
        "Brussels",
        "Munich",
    ]
    city_index = {name: i for i, name in enumerate(cities)}

    # Required total days (including flight-day counting rule)
    required_days = {
        "Copenhagen": 5,
        "Geneva": 3,
        "Mykonos": 2,
        "Naples": 4,
        "Prague": 2,
        "Dubrovnik": 3,
        "Athens": 4,
        "Santorini": 5,
        "Brussels": 4,
        "Munich": 5,
    }

    # Direct flight edges (undirected)
    flight_pairs = [
        ("Copenhagen", "Dubrovnik"),
        ("Brussels", "Copenhagen"),
        ("Prague", "Geneva"),
        ("Athens", "Geneva"),
        ("Naples", "Dubrovnik"),
        ("Athens", "Dubrovnik"),
        ("Geneva", "Mykonos"),
        ("Naples", "Mykonos"),
        ("Naples", "Copenhagen"),
        ("Munich", "Mykonos"),
        ("Naples", "Athens"),
        ("Prague", "Athens"),
        ("Santorini", "Geneva"),
        ("Athens", "Santorini"),
        ("Naples", "Munich"),
        ("Prague", "Copenhagen"),
        ("Brussels", "Naples"),
        ("Athens", "Mykonos"),
        ("Athens", "Copenhagen"),
        ("Naples", "Geneva"),
        ("Dubrovnik", "Munich"),
        ("Brussels", "Munich"),
        ("Prague", "Brussels"),
        ("Brussels", "Athens"),
        ("Athens", "Munich"),
        ("Geneva", "Munich"),
        ("Copenhagen", "Munich"),
        ("Brussels", "Geneva"),
        ("Copenhagen", "Geneva"),
        ("Prague", "Munich"),
        ("Copenhagen", "Santorini"),
        ("Naples", "Santorini"),
        ("Geneva", "Dubrovnik"),
    ]

    # Build undirected adjacency as pairs of indices
    edges = set()
    for a, b in flight_pairs:
        if a not in city_index or b not in city_index:
            raise ValueError(f"Unknown city in flight pair: {(a, b)}")
        ia, ib = city_index[a], city_index[b]
        edges.add((ia, ib))
        edges.add((ib, ia))

    # Z3 setup
    days = 28
    s = Solver()

    # City assignment per day: c[d] in [0..len(cities)-1]
    c = [Int(f"c_{d}") for d in range(1, days + 1)]
    for d in range(days):
        s.add(And(c[d] >= 0, c[d] < len(cities)))

    # Flight constraints: if c[d] != c[d-1], it must be a direct flight
    for d in range(1, days):
        # Or same city, or an allowed edge
        allowed_transitions = [And(c[d-1] == i, c[d] == j) for (i, j) in edges]
        s.add(Or(c[d] == c[d-1], Or(*allowed_transitions)))

    # In-city membership per day considering flight-day rule
    # in_city[city][day] is True if on that day, you're in the city
    # Rule:
    #   - If day == 1: in_city = (c[1] == city)
    #   - If day > 1: in_city = (c[day] == city) or (c[day-1] == city and c[day] != c[day-1])  # departure day
    in_city = [[Bool(f"in_{city}_{d+1}") for d in range(days)] for city in range(len(cities))]
    for i in range(len(cities)):
        # Day 1
        s.add(in_city[i][0] == (c[0] == i))
        # Days 2..28
        for d in range(1, days):
            s.add(
                in_city[i][d] ==
                Or(c[d] == i, And(c[d-1] == i, c[d] != c[d-1]))
            )

    # Required day counts per city
    for name, req in required_days.items():
        i = city_index[name]
        s.add(Sum([If(in_city[i][d], 1, 0) for d in range(days)]) == req)

    # Windows:
    # - Meet friend in Copenhagen between day 11 and 15
    cph = city_index["Copenhagen"]
    s.add(Or([in_city[cph][d-1] for d in range(11, 16)]))

    # - Workshop in Athens between day 8 and 11
    ath = city_index["Athens"]
    s.add(Or([in_city[ath][d-1] for d in range(8, 12)]))

    # - Visit relatives in Naples between day 5 and 8
    nap = city_index["Naples"]
    s.add(Or([in_city[nap][d-1] for d in range(5, 9)]))

    # - Conference in Mykonos on day 27 and 28
    myk = city_index["Mykonos"]
    s.add(in_city[myk][26])  # day 27
    s.add(in_city[myk][27])  # day 28

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found under given constraints.")

    m = s.model()
    itinerary = []
    for d in range(days):
        idx = m.evaluate(c[d]).as_long()
        itinerary.append({"day": d + 1, "city": cities[idx]})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))
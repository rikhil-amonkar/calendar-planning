import json
from z3 import *

def solve_itinerary():
    # Parameters
    cities = ["Geneva", "Split", "Helsinki", "Reykjavik", "Vilnius"]
    city_index = {name: i for i, name in enumerate(cities)}
    num_cities = len(cities)
    total_days = 12

    # Required stay durations per city
    required_days = {
        "Split": 2,
        "Helsinki": 2,
        "Reykjavik": 3,
        "Vilnius": 3,
        "Geneva": 6,
    }

    # Windows (inclusive): must be present in these cities on these days
    vilnius_window = (7, 9)      # days 7-9
    reykjavik_window = (10, 12)  # days 10-12

    # Direct flight connections (undirected)
    direct_flights = [
        ("Split", "Helsinki"),
        ("Geneva", "Split"),
        ("Geneva", "Helsinki"),
        ("Helsinki", "Reykjavik"),
        ("Vilnius", "Helsinki"),
        ("Split", "Vilnius"),
    ]
    allowed_transitions = set()
    for a, b in direct_flights:
        i, j = city_index[a], city_index[b]
        allowed_transitions.add((i, j))
        allowed_transitions.add((j, i))

    # SMT Model
    opt = Optimize()

    # loc[d] is the city (index) at the end of day d; d=0..12 (day 0 is the initial city before day 1)
    loc = [Int(f"loc_{d}") for d in range(0, total_days + 1)]
    for d in range(total_days + 1):
        opt.add(And(loc[d] >= 0, loc[d] < num_cities))

    # flight[d] is True if a flight occurs on day d (1..12), i.e., loc[d] != loc[d-1]
    flight = [Bool(f"flight_{d}") for d in range(1, total_days + 1)]
    for d in range(1, total_days + 1):
        opt.add(flight[d - 1] == (loc[d] != loc[d - 1]))
        # If a flight occurs on day d, it must be along a direct connection
        opt.add(Implies(
            flight[d - 1],
            Or([And(loc[d - 1] == i, loc[d] == j) for (i, j) in allowed_transitions])
        ))

    # presence[c, d] is True iff city c is one of the cities occupied on day d
    # If a flight occurs on day d, the traveler is in both loc[d-1] and loc[d] on that day
    presence = {}
    for c in range(num_cities):
        for d in range(1, total_days + 1):
            presence[(c, d)] = Bool(f"presence_{c}_{d}")
            opt.add(presence[(c, d)] == Or(loc[d] == c, loc[d - 1] == c))

    # Each day contributes presence in either 1 city (if no flight) or 2 cities (if flight)
    for d in range(1, total_days + 1):
        opt.add(
            Sum([If(presence[(c, d)], 1, 0) for c in range(num_cities)]) ==
            If(flight[d - 1], 2, 1)
        )

    # Duration constraints per city
    for name, req_days in required_days.items():
        c = city_index[name]
        opt.add(Sum([If(presence[(c, d)], 1, 0) for d in range(1, total_days + 1)]) == req_days)

    # Window constraints: must be present in Vilnius on days 7-9
    vilnius_idx = city_index["Vilnius"]
    for d in range(vilnius_window[0], vilnius_window[1] + 1):
        opt.add(presence[(vilnius_idx, d)])

    # Window constraints: must be present in Reykjavik on days 10-12
    reykjavik_idx = city_index["Reykjavik"]
    for d in range(reykjavik_window[0], reykjavik_window[1] + 1):
        opt.add(presence[(reykjavik_idx, d)])

    # Optional global consistency: total presence count equals total_days + number of flights
    total_flights = Sum([If(f, 1, 0) for f in flight])
    total_presence = Sum([If(presence[(c, d)], 1, 0) for c in range(num_cities) for d in range(1, total_days + 1)])
    opt.add(total_presence == total_days + total_flights)

    # Optimize for minimal number of flights (prefer fewer commuting days)
    opt.minimize(total_flights)

    if opt.check() != sat:
        raise RuntimeError("No feasible itinerary could be found under the given constraints.")

    model = opt.model()

    # Extract end-of-day locations for days 1..12
    end_city = [model.evaluate(loc[d]).as_long() for d in range(1, total_days + 1)]

    # Build compressed itinerary by consecutive segments of the same end-of-day city
    itinerary = []
    seg_start = 1
    current = end_city[0]
    for d in range(2, total_days + 1):
        if end_city[d - 1] != current:
            itinerary.append({
                "day_range": f"Day {seg_start}-{d-1}",
                "place": cities[current]
            })
            seg_start = d
            current = end_city[d - 1]
    # Add final segment
    itinerary.append({
        "day_range": f"Day {seg_start}-{total_days}",
        "place": cities[current]
    })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result))
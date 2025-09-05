import json
from z3 import *

def solve_itinerary():
    # Cities and indices
    cities = ["Barcelona", "Oslo", "Venice", "Split", "Brussels", "Stuttgart", "Copenhagen"]
    city_idx = {c: i for i, c in enumerate(cities)}
    n_days = 16

    # Required presence durations (days counted with flight-day overlap rule)
    req_days = {
        "Oslo": 2,
        "Stuttgart": 3,
        "Venice": 4,
        "Split": 4,
        "Barcelona": 3,
        "Brussels": 3,
        "Copenhagen": 3,
    }

    # Direct flight edges (bidirectional)
    edge_pairs = [
        ("Venice", "Stuttgart"),
        ("Oslo", "Brussels"),
        ("Split", "Copenhagen"),
        ("Barcelona", "Copenhagen"),
        ("Barcelona", "Venice"),
        ("Brussels", "Venice"),
        ("Barcelona", "Stuttgart"),
        ("Copenhagen", "Brussels"),
        ("Oslo", "Split"),
        ("Oslo", "Venice"),
        ("Barcelona", "Split"),
        ("Oslo", "Copenhagen"),
        ("Barcelona", "Oslo"),
        ("Copenhagen", "Stuttgart"),
        ("Split", "Stuttgart"),
        ("Copenhagen", "Venice"),
        ("Barcelona", "Brussels"),
    ]
    edges = set()
    for a, b in edge_pairs:
        ai, bi = city_idx[a], city_idx[b]
        edges.add((ai, bi))
        edges.add((bi, ai))

    # Z3 variables
    start = [Int(f"start_{d+1}") for d in range(n_days)]  # city at the start of day d+1
    end   = [Int(f"end_{d+1}")   for d in range(n_days)]  # city at the end of day d+1
    flight = [Bool(f"flight_{d+1}") for d in range(n_days)]  # whether a flight occurs on day d+1

    s = Solver()

    # Domain constraints
    for d in range(n_days):
        s.add(And(start[d] >= 0, start[d] < len(cities)))
        s.add(And(end[d] >= 0, end[d] < len(cities)))
        s.add(flight[d] == (start[d] != end[d]))

    # Daily continuity: end of day d equals start of day d+1
    for d in range(n_days - 1):
        s.add(end[d] == start[d + 1])

    # Flights must respect direct edges when they occur
    def is_direct(a, b):
        return Or([And(a == i, b == j) for (i, j) in edges]) if edges else False

    for d in range(n_days):
        s.add(Implies(flight[d], is_direct(start[d], end[d])))

    # Presence per city per day: present if either start or end equals the city
    presence = {
        c: [Or(start[d] == city_idx[c], end[d] == city_idx[c]) for d in range(n_days)]
        for c in cities
    }

    # Duration constraints per city
    for c in cities:
        s.add(Sum([If(presence[c][d], 1, 0) for d in range(n_days)]) == req_days[c])

    # Total flights equals sum of overlap needed: sum(req_days) - total_days
    # sum(req_days) = 22, total_days = 16 -> flights = 6
    s.add(Sum([If(flight[d], 1, 0) for d in range(n_days)]) == 6)

    # Barcelona show: present on days 1-3
    for d in [0, 1, 2]:
        s.add(presence["Barcelona"][d])

    # Oslo meet: present on day 3 or day 4
    s.add(Or(presence["Oslo"][2], presence["Oslo"][3]))

    # Brussels meet: present on one of days 9-11
    s.add(Or(presence["Brussels"][8], presence["Brussels"][9], presence["Brussels"][10]))

    # Solve
    if s.check() != sat:
        return {"error": "No feasible itinerary satisfying all constraints."}

    m = s.model()

    # Extract start/end per day
    start_vals = [m.evaluate(start[d]).as_long() for d in range(n_days)]
    end_vals = [m.evaluate(end[d]).as_long() for d in range(n_days)]
    flight_vals = [is_true(m.evaluate(flight[d])) for d in range(n_days)]

    # Build human-readable per-day entries
    day_entries = []
    for d in range(n_days):
        if flight_vals[d]:
            place = f"{cities[start_vals[d]]} -> {cities[end_vals[d]]}"
        else:
            place = f"{cities[start_vals[d]]}"
        day_entries.append((d + 1, place))

    # Merge consecutive days with identical place descriptor into ranges
    itinerary = []
    if day_entries:
        cur_place = day_entries[0][1]
        range_start = day_entries[0][0]
        last_day = day_entries[0][0]
        for (day, place) in day_entries[1:]:
            if place == cur_place and day == last_day + 1:
                last_day = day
            else:
                itinerary.append({
                    "day_range": f"Day {range_start}-{last_day}",
                    "place": cur_place
                })
                cur_place = place
                range_start = day
                last_day = day
        itinerary.append({
            "day_range": f"Day {range_start}-{last_day}",
            "place": cur_place
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False))
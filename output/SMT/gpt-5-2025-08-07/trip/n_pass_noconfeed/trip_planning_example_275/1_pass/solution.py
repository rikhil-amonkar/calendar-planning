import json
from z3 import *

def solve_itinerary():
    # Input variables (can be adjusted as needed)
    cities = ["Vilnius", "Split", "Madrid", "Santorini"]
    city_index = {name: i for i, name in enumerate(cities)}
    total_days = 14

    # Desired stay counts (days are counted with flight-day overlap rule)
    desired_days = {
        "Vilnius": 4,
        "Split": 5,
        "Madrid": 6,
        "Santorini": 2
    }

    # Conference requirement: must be in Santorini on Day 13 and Day 14
    conference_city = "Santorini"
    conference_days = [13, 14]

    # Direct flights (undirected)
    direct_flights = {
        ("Vilnius", "Split"),
        ("Split", "Madrid"),
        ("Madrid", "Santorini")
    }
    # Symmetrize
    direct_flights |= {(b, a) for (a, b) in list(direct_flights)}

    # Helper to check adjacency
    def is_adj(a, b):
        if a == b:
            return True
        return (cities[a], cities[b]) in direct_flights

    # Z3 model
    s = Solver()

    # Location at start of day d: loc[d], for d in 1..(total_days+1)
    # loc[total_days+1] is the location at the start of Day total_days+1 (end of Day total_days)
    loc = [Int(f"loc_{d}") for d in range(1, total_days + 2)]

    # Domain constraints
    for d in range(total_days + 1):
        s.add(And(loc[d] >= 0, loc[d] < len(cities)))

    # Transitions: either stay or take a direct flight
    # If loc changes between day d and d+1, it must be a direct flight
    for d in range(1, total_days + 1):
        allowed = Or(loc[d - 1] == loc[d])
        # Add all allowed direct transitions
        allowed_edges = []
        for a in range(len(cities)):
            for b in range(len(cities)):
                if a != b and is_adj(a, b):
                    allowed_edges.append(And(loc[d - 1] == a, loc[d] == b))
        if allowed_edges:
            allowed = Or(allowed, Or(*allowed_edges))
        s.add(allowed)

    # Flight-day boolean: flight occurs on day d if loc[d] != loc[d+1]
    flight = [Bool(f"flight_{d}") for d in range(1, total_days + 1)]
    for d in range(1, total_days + 1):
        s.add(flight[d - 1] == (loc[d - 1] != loc[d]))

    # In-city day booleans: in_city[c][d] is True if day d counts towards city c
    # Rule: a day counts for city c if either:
    # - You start day d in c (loc[d] == c), or
    # - You fly into c by the end of day d (flight[d] and loc[d+1] == c).
    in_city = [[Bool(f"in_{c}_{d}") for d in range(1, total_days + 1)] for c in range(len(cities))]
    for c in range(len(cities)):
        for d in range(1, total_days + 1):
            s.add(in_city[c][d - 1] == Or(loc[d - 1] == c, And(flight[d - 1], loc[d] == c)))

    # Desired day counts per city
    for name, cnt in desired_days.items():
        c = city_index[name]
        s.add(Sum([If(in_city[c][d], 1, 0) for d in range(total_days)]) == cnt)

    # Conference constraint: must be in Santorini (counting rule) on Day 13 and Day 14
    san = city_index[conference_city]
    for d in conference_days:
        s.add(in_city[san][d - 1] == True)

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    m = s.model()

    # Extract locations for days 1..(total_days+1)
    loc_vals = [m.evaluate(loc[d]).as_long() for d in range(total_days + 1)]

    # Build itinerary segments with overlapping endpoints on flight days
    # A "segment" spans from prev_break to next_break, where breaks are days with a flight
    breaks = [1]
    for d in range(1, total_days + 1):
        if loc_vals[d - 1] != loc_vals[d]:
            breaks.append(d)
    if breaks[-1] != total_days:
        breaks.append(total_days)

    # Construct segments:
    # For segment between breaks[i] .. breaks[i+1], label with the city at the end day (breaks[i+1])
    itinerary = []
    for i in range(len(breaks) - 1):
        start_day = breaks[i]
        end_day = breaks[i + 1]
        # City label is the location at the end of the segment day (still the "prior" city due to overlap)
        city_label = cities[loc_vals[end_day - 1]]
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city_label
        })

    # Output as JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_itinerary()
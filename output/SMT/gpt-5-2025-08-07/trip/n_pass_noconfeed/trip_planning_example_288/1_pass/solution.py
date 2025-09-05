import json
from z3 import *

def plan_trip():
    # Input variables (modifiable)
    total_days = 15
    city_names = ["Stuttgart", "Manchester", "Madrid", "Vienna"]
    S, M, Md, V = 0, 1, 2, 3  # Enumerated city indices
    required_days = {
        S: 5,  # Stuttgart
        M: 7,  # Manchester
        Md: 4, # Madrid
        V: 2   # Vienna
    }
    # Windows (inclusive day numbers, 1-based)
    wedding_days = list(range(1, 8))   # Must be in Manchester on Days 1-7
    workshop_days = list(range(11, 16))# Must be in Stuttgart on Days 11-15

    # Direct flights (bidirectional)
    direct_edges = set([
        (V, S), (S, V),
        (M, V), (V, M),
        (Md, V), (V, Md),
        (M, S), (S, M),
        (M, Md), (Md, M)
    ])

    # Z3 setup
    N = total_days
    loc = [Int(f"loc_{d}") for d in range(N)]   # start city of day d
    dest = [Int(f"dest_{d}") for d in range(N)] # destination city of day d (if flight occurs)
    fly = [Bool(f"fly_{d}") for d in range(N)]  # whether a flight occurs on day d

    opt = Optimize()

    # Domain constraints
    for d in range(N):
        # Cities in range
        opt.add(And(loc[d] >= 0, loc[d] < len(city_names)))
        opt.add(And(dest[d] >= 0, dest[d] < len(city_names)))

        # Flight semantics
        # If fly[d] then dest != loc and the edge must be direct.
        # If not fly[d], then dest[d] == loc[d].
        edge_allowed = Or(*[And(loc[d] == i, dest[d] == j) for (i, j) in direct_edges]) if direct_edges else False
        opt.add(Implies(fly[d], And(dest[d] != loc[d], edge_allowed)))
        opt.add(Implies(Not(fly[d]), dest[d] == loc[d]))

        # Continuity: The next day's start city is today's destination
        if d < N - 1:
            opt.add(loc[d + 1] == dest[d])

    # Presence helper: presence of city c on day d (counts flight rule)
    def presence_count_for_city(c):
        return Sum([
            If(loc[d] == c, 1, 0) + If(And(fly[d], dest[d] == c), 1, 0)
            for d in range(N)
        ])

    # Duration constraints
    for c, req in required_days.items():
        opt.add(presence_count_for_city(c) == req)

    # Wedding: must be in Manchester on days 1-7
    for day in wedding_days:
        idx = day - 1
        opt.add(Or(loc[idx] == M, And(fly[idx], dest[idx] == M)))

    # Workshop: must be in Stuttgart on days 11-15
    for day in workshop_days:
        idx = day - 1
        opt.add(Or(loc[idx] == S, And(fly[idx], dest[idx] == S)))

    # Optional: minimize total flights
    total_flights = Sum([If(fly[d], 1, 0) for d in range(N)])
    opt.minimize(total_flights)

    if opt.check() != sat:
        return {"itinerary": []}

    model = opt.model()

    # Build presence per day per city (to compute ranges for output)
    present = {c: [] for c in range(len(city_names))}
    for d in range(N):
        l = model[loc[d]].as_long()
        f = is_true(model[fly[d]])
        dp = model[dest[d]].as_long()
        # Always present in start city
        present[l].append(d + 1)  # store 1-based day
        # If flight, also present in destination
        if f:
            present[dp].append(d + 1)

    # Deduplicate and sort per city days (in case of any duplication)
    for c in present:
        present[c] = sorted(set(present[c]))

    # Convert presence days per city into contiguous ranges
    def days_to_ranges(days_list):
        if not days_list:
            return []
        ranges = []
        start = prev = days_list[0]
        for day in days_list[1:]:
            if day == prev + 1:
                prev = day
            else:
                ranges.append((start, prev))
                start = prev = day
        ranges.append((start, prev))
        return ranges

    segments = []
    for c in range(len(city_names)):
        for (a, b) in days_to_ranges(present[c]):
            segments.append({
                "start": a,
                "end": b,
                "place": city_names[c]
            })

    # Sort segments by start day for chronological order
    segments.sort(key=lambda x: (x["start"], x["end"], x["place"]))

    # Format for output
    itinerary = []
    for seg in segments:
        day_range = f"Day {seg['start']}-{seg['end']}"
        itinerary.append({"day_range": day_range, "place": seg["place"]})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = plan_trip()
    print(json.dumps(result, ensure_ascii=False))
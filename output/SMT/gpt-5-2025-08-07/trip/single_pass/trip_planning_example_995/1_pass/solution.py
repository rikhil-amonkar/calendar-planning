import json
from z3 import *

def solve_itinerary():
    # Cities and required durations (in days, inclusive of flight-day overlaps)
    cities = ["Oslo", "Stuttgart", "Venice", "Split", "Barcelona", "Brussels", "Copenhagen"]
    idx = {c: i for i, c in enumerate(ccities := cities)}  # alias for brevity
    duration = {
        "Oslo": 2,
        "Stuttgart": 3,
        "Venice": 4,
        "Split": 4,
        "Barcelona": 3,
        "Brussels": 3,
        "Copenhagen": 3
    }
    total_days = 16

    # Direct flight pairs (undirected)
    direct_pairs = [
        ("Venice", "Stuttgart"), ("Oslo", "Brussels"), ("Split", "Copenhagen"),
        ("Barcelona", "Copenhagen"), ("Barcelona", "Venice"), ("Brussels", "Venice"),
        ("Barcelona", "Stuttgart"), ("Copenhagen", "Brussels"), ("Oslo", "Split"),
        ("Oslo", "Venice"), ("Barcelona", "Split"), ("Oslo", "Copenhagen"),
        ("Barcelona", "Oslo"), ("Copenhagen", "Stuttgart"), ("Split", "Stuttgart"),
        ("Copenhagen", "Venice"), ("Barcelona", "Brussels")
    ]
    # Build symmetric adjacency set of index pairs
    edges = set()
    for a, b in direct_pairs:
        ia, ib = idx[a], idx[b]
        edges.add((ia, ib))
        edges.add((ib, ia))

    n = len(cities)

    # Z3 Variables
    order = [Int(f"order_{k}") for k in range(n)]            # permutation of cities in visit order
    start = [Int(f"start_{i}") for i in range(n)]            # inclusive start day for city i
    end = [Int(f"end_{i}") for i in range(n)]                # inclusive end day for city i

    s = Solver()

    # Order is a permutation of 0..n-1
    for k in range(n):
        s.add(order[k] >= 0, order[k] < n)
    s.add(Distinct(order))

    # Barcelona must be visited first to attend the Day 1-3 show in Barcelona
    s.add(order[0] == idx["Barcelona"])

    # Duration constraints for each city
    for i, c in enumerate(cities):
        d = duration[c]
        s.add(end[i] == start[i] + d - 1)

    # Chain the cities so that flying day overlaps (start of next equals end of current)
    s.add(start[order[0]] == 1)                 # Trip starts Day 1 in first city
    for k in range(n - 1):
        # Overlapping flight-day constraint
        s.add(start[order[k + 1]] == end[order[k]])

        # Direct flight constraint between consecutive cities
        allowed = [And(order[k] == i, order[k + 1] == j) for (i, j) in edges]
        s.add(Or(*allowed))

    # End of the last city must be Day 16 (this follows from sums but we assert explicitly)
    s.add(end[order[-1]] == total_days)

    # Attendance constraints:
    # - Barcelona show from Day 1 to Day 3 (already ensured by being first with duration 3,
    #   but we explicitly assert end == 3 for clarity)
    s.add(start[idx["Barcelona"]] == 1)
    s.add(end[idx["Barcelona"]] == 3)

    # - Meet friends in Oslo between Day 3 and Day 4 (be in Oslo on Day 3 or Day 4)
    s.add(start[idx["Oslo"]] <= 4)
    s.add(end[idx["Oslo"]] >= 3)

    # - Meet a friend in Brussels between Day 9 and Day 11 (be in Brussels on any of 9,10,11)
    s.add(start[idx["Brussels"]] <= 11)
    s.add(end[idx["Brussels"]] >= 9)

    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found with the given constraints.")

    m = s.model()

    # Extract concrete order to help build a sensible day-by-day output order
    order_vals = [m.evaluate(order[k]).as_long() for k in range(n)]
    visit_order = [cities[i] for i in order_vals]
    pos_in_order = {city: i for i, city in enumerate(visit_order)}

    # Extract start/end for each city
    start_day = {cities[i]: m.evaluate(start[i]).as_long() for i in range(n)}
    end_day = {cities[i]: m.evaluate(end[i]).as_long() for i in range(n)}

    # Build the day-place mappings:
    # For each day, include all cities whose intervals cover that day.
    # This naturally includes both cities on flight days (the overlapping boundary).
    itinerary = []
    for day in range(1, total_days + 1):
        todays_cities = [c for c in cities if start_day[c] <= day <= end_day[c]]
        # Sort cities by their visit order so overlapping days list previous city first
        todays_cities.sort(key=lambda c: pos_in_order[c])
        for c in todays_cities:
            itinerary.append({"day": day, "city": c})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False))
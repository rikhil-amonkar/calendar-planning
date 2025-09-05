import json
from z3 import *

def main():
    # Cities
    cities = ["Stuttgart", "Edinburgh", "Athens", "Split", "Krakow", "Venice", "Mykonos"]

    # Durations desired in each city (inclusive of arrival/departure flight days)
    durations = {
        "Stuttgart": 3,
        "Edinburgh": 4,
        "Athens": 4,
        "Split": 2,
        "Krakow": 4,
        "Venice": 5,
        "Mykonos": 4
    }

    # Total trip days
    TOTAL_DAYS = 20

    # Direct flight connections (undirected)
    direct_flights = [
        ("Krakow", "Split"),
        ("Split", "Athens"),
        ("Edinburgh", "Krakow"),
        ("Venice", "Stuttgart"),
        ("Krakow", "Stuttgart"),
        ("Edinburgh", "Stuttgart"),
        ("Stuttgart", "Athens"),
        ("Venice", "Edinburgh"),
        ("Athens", "Mykonos"),
        ("Venice", "Athens"),
        ("Stuttgart", "Split"),
        ("Edinburgh", "Athens"),
    ]

    # Build neighbor map
    neighbors = {c: set() for c in cities}
    for a, b in direct_flights:
        neighbors[a].add(b)
        neighbors[b].add(a)

    # Z3 variables
    s = Solver()

    # Position of each city in the travel order (0..6)
    pos = {c: Int(f"pos_{c.replace(' ', '_').lower()}") for c in cities}
    for c in cities:
        s.add(pos[c] >= 0, pos[c] <= len(cities) - 1)
    s.add(Distinct([pos[c] for c in cities]))

    # Entry and exit days for each city (1..20)
    entry = {c: Int(f"entry_{c.replace(' ', '_').lower()}") for c in cities}
    exitd = {c: Int(f"exit_{c.replace(' ', '_').lower()}") for c in cities}
    for c in cities:
        s.add(entry[c] >= 1, entry[c] <= TOTAL_DAYS)
        s.add(exitd[c] >= 1, exitd[c] <= TOTAL_DAYS)
        s.add(exitd[c] >= entry[c])
        # Duration constraint (inclusive days)
        s.add(exitd[c] - entry[c] + 1 == durations[c])

    # Windows and fixed-day constraints:
    # - Stuttgart: must be there Days 11-13 exactly (workshop)
    s.add(entry["Stuttgart"] == 11)
    s.add(exitd["Stuttgart"] == 13)

    # - Split: 2 days, meet friends Day 13-14
    s.add(entry["Split"] == 13)
    s.add(exitd["Split"] == 14)

    # - Krakow: 4 days, meet friend between Day 8 and Day 11
    s.add(entry["Krakow"] == 8)
    s.add(exitd["Krakow"] == 11)

    # Path continuity and direct flight constraints:
    # First city's entry is day 1, last city's exit is day 20
    for c in cities:
        s.add(Implies(pos[c] == 0, entry[c] == 1))
        s.add(Implies(pos[c] == len(cities) - 1, exitd[c] == TOTAL_DAYS))

    # For each city, the next city (if not last) must be a direct neighbor
    for a in cities:
        # If not the last in order, enforce that the next position is one of the neighbors
        next_is_neighbor = [pos[b] == pos[a] + 1 for b in neighbors[a]]
        s.add(Or(pos[a] == len(cities) - 1, Or(next_is_neighbor)))
        # If some neighbor is exactly next, then time continuity holds: exit[a] == entry[neighbor]
        for b in neighbors[a]:
            s.add(Implies(pos[b] == pos[a] + 1, exitd[a] == entry[b]))

    # Also enforce predecessor adjacency (optional but tightens model)
    for a in cities:
        prev_is_neighbor = [pos[b] == pos[a] - 1 for b in neighbors[a]]
        s.add(Or(pos[a] == 0, Or(prev_is_neighbor)))

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": [], "status": "unsat"}))
        return

    m = s.model()

    # Extract solution
    solution = []
    for c in cities:
        solution.append({
            "city": c,
            "pos": m[pos[c]].as_long(),
            "entry": m[entry[c]].as_long(),
            "exit": m[exitd[c]].as_long()
        })

    # Sort by travel order
    solution.sort(key=lambda x: x["pos"])

    itinerary = []
    for seg in solution:
        itinerary.append({
            "day_range": f"Day {seg['entry']}-{seg['exit']}",
            "place": seg["city"]
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
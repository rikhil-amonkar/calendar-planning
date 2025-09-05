import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = [
        "Santorini", "Valencia", "Madrid", "Seville", "Bucharest",
        "Vienna", "Riga", "Tallinn", "Krakow", "Frankfurt"
    ]
    idx = {c: i for i, c in enumerate(cities)}
    n = len(cities)

    # Durations required in each city (total sums to 36, with 9 overlaps on flight days to match 27 calendar days)
    durations = {
        "Santorini": 3,
        "Valencia": 4,
        "Madrid": 2,
        "Seville": 2,
        "Bucharest": 3,
        "Vienna": 4,
        "Riga": 4,
        "Tallinn": 5,
        "Krakow": 5,
        "Frankfurt": 4
    }

    # Fixed presence windows (inclusive), aligned with event requirements
    fixed_windows = {
        "Vienna":   (3, 6),   # wedding between day 3 and day 6 inclusive
        "Madrid":   (6, 7),   # show day 6 to 7
        "Krakow":   (11, 15), # meet friends between day 11 and day 15
        "Riga":     (20, 23), # conference during day 20 to 23
        "Tallinn":  (23, 27)  # workshop between day 23 and day 27
    }

    # Allowed direct flights (directed where specified, otherwise undirected)
    undirected_pairs = [
        ("Vienna", "Bucharest"),
        ("Santorini", "Madrid"),
        ("Seville", "Valencia"),
        ("Vienna", "Seville"),
        ("Madrid", "Valencia"),
        ("Bucharest", "Riga"),
        ("Valencia", "Bucharest"),
        ("Santorini", "Bucharest"),
        ("Vienna", "Valencia"),
        ("Vienna", "Madrid"),
        ("Valencia", "Krakow"),
        ("Valencia", "Frankfurt"),
        ("Krakow", "Frankfurt"),
        ("Vienna", "Krakow"),
        ("Vienna", "Frankfurt"),
        ("Madrid", "Seville"),
        ("Santorini", "Vienna"),
        ("Vienna", "Riga"),
        ("Frankfurt", "Tallinn"),
        ("Frankfurt", "Bucharest"),
        ("Madrid", "Bucharest"),
        ("Frankfurt", "Riga"),
        ("Madrid", "Frankfurt"),
    ]
    directed_pairs = [
        ("Riga", "Tallinn"),  # explicitly directed
    ]

    allowed = set()
    for a, b in undirected_pairs:
        allowed.add((idx[a], idx[b]))
        allowed.add((idx[b], idx[a]))
    for a, b in directed_pairs:
        allowed.add((idx[a], idx[b]))

    # Z3 variables
    s = [Int(f"s_{c}") for c in cities]  # start days
    e = [Int(f"e_{c}") for c in cities]  # end days
    order = [Int(f"ord_{c}") for c in cities]  # 0..9 permutation

    solver = Solver()

    # Domains
    for i, c in enumerate(cities):
        solver.add(s[i] >= 1, s[i] <= 27)
        solver.add(e[i] >= 1, e[i] <= 27)
        solver.add(e[i] == s[i] + durations[c] - 1)
        solver.add(order[i] >= 0, order[i] < n)

    # All-different order (permutation of positions 0..9)
    solver.add(Distinct(order))

    # First city starts on day 1, last city ends on day 27
    for i in range(n):
        solver.add(Implies(order[i] == 0, s[i] == 1))
        solver.add(Implies(order[i] == n - 1, e[i] == 27))

    # Consecutive adjacency must have overlapping boundary (flight day) and be a direct flight
    # Prevent non-edges from being consecutive
    for a in range(n):
        for b in range(n):
            if a == b:
                continue
            # If b immediately follows a in order, then end of a equals start of b
            solver.add(Implies(order[b] == order[a] + 1, e[a] == s[b]))
            # Enforce direct flight availability for consecutive cities
            if (a, b) not in allowed:
                solver.add(order[b] != order[a] + 1)

    # Non-adjacent cities must not overlap (only overlaps allowed are on flight days between consecutive cities)
    for a in range(n):
        for b in range(a + 1, n):
            not_consecutive = And(order[a] + 1 != order[b], order[b] + 1 != order[a])
            # No overlap if not consecutive
            solver.add(Implies(not_consecutive, Or(e[a] < s[b], e[b] < s[a])))

    # Fixed windows for specific cities
    for cname, (fs, fe) in fixed_windows.items():
        i = idx[cname]
        solver.add(s[i] == fs)
        solver.add(e[i] == fe)

    # Solve
    if solver.check() != sat:
        raise RuntimeError("No feasible itinerary found with the given constraints.")

    m = solver.model()

    # Extract solution and order
    itinerary = []
    # Build list of (order, city, start, end)
    trip = []
    for c in cities:
        i = idx[c]
        trip.append((m[order[i]].as_long(), c, m[s[i]].as_long(), m[e[i]].as_long()))
    trip.sort(key=lambda x: x[0])

    for (_, city, start, end) in trip:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False))
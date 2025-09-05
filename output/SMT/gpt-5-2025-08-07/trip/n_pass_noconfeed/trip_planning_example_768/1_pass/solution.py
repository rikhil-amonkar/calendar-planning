import json
from z3 import *

def main():
    # Define cities and parameters
    cities = ["Mykonos", "Nice", "London", "Copenhagen", "Oslo", "Tallinn"]
    city_index = {name: i for i, name in enumerate(cities)}
    n_days = 16

    # Trip requirements (as input-like variables)
    required_days = {
        "Mykonos": 4,
        "Nice": 3,
        "London": 2,
        "Copenhagen": 3,
        "Oslo": 5,
        "Tallinn": 4,
    }

    # Conference days (must be in Nice on these days)
    conference_days_in_nice = [14, 16]

    # Friend meeting window in Oslo (must be in Oslo on at least one of these days)
    meet_friend_oslo_window = list(range(10, 15))  # inclusive 10..14

    # Direct flight pairs (undirected)
    direct_edges_input = [
        ("London", "Copenhagen"),
        ("Copenhagen", "Tallinn"),
        ("Tallinn", "Oslo"),
        ("Mykonos", "London"),
        ("Oslo", "Nice"),
        ("London", "Nice"),
        ("Mykonos", "Nice"),
        ("London", "Oslo"),
        ("Copenhagen", "Nice"),
        ("Copenhagen", "Oslo"),
    ]
    allowed_pairs = set()
    for a, b in direct_edges_input:
        ia, ib = city_index[a], city_index[b]
        allowed_pairs.add((ia, ib))
        allowed_pairs.add((ib, ia))
    allowed_pairs = list(allowed_pairs)

    # Z3 variables
    city_end = [Int(f"city_end_{d}") for d in range(1, n_days + 1)]  # city at end of day d
    present = [[Int(f"present_{c}_{d}") for d in range(1, n_days + 1)] for c in range(len(cities))]

    s = Solver()

    # Domain constraints for city_end and present variables
    for d in range(n_days):
        s.add(And(city_end[d] >= 0, city_end[d] < len(cities)))
    for c in range(len(cities)):
        for d in range(n_days):
            s.add(And(present[c][d] >= 0, present[c][d] <= 1))

    # Movement constraints: if city changes between day d-1 and d, it must be a direct flight
    for d in range(1, n_days):  # index 1..15 (day 2..16)
        prev, curr = city_end[d - 1], city_end[d]
        allowed_change = Or(prev == curr, Or([And(prev == a, curr == b) for (a, b) in allowed_pairs]))
        s.add(allowed_change)

    # Presence definition:
    # present[c][d] == 1 iff:
    #   - city_end[d] == c
    #   OR
    #   - (d>0) and city_end[d-1] == c and city_end[d] != c  (departing from c on day d+1 in 1-based indexing)
    for c in range(len(cities)):
        # Day 1
        s.add(present[c][0] == If(city_end[0] == c, 1, 0))
        # Days 2..16
        for d in range(1, n_days):
            s.add(present[c][d] == If(Or(city_end[d] == c, And(city_end[d - 1] == c, city_end[d] != c)), 1, 0))

    # Duration constraints for each city
    for name, req in required_days.items():
        idx = city_index[name]
        s.add(Sum(present[idx]) == req)

    # Conference in Nice on day 14 and day 16
    nice_idx = city_index["Nice"]
    for conf_day in conference_days_in_nice:
        s.add(present[nice_idx][conf_day - 1] == 1)  # 1-based to 0-based indexing

    # Meet friend in Oslo between day 10..14 inclusive
    oslo_idx = city_index["Oslo"]
    s.add(Sum([present[oslo_idx][d - 1] for d in meet_friend_oslo_window]) >= 1)

    # Consistency: total flights equals sum(required_days) - n_days (because travel days count for both cities)
    total_required = sum(required_days.values())
    flights = [If(city_end[d] != city_end[d - 1], 1, 0) for d in range(1, n_days)]
    s.add(Sum(flights) == total_required - n_days)

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    m = s.model()

    # Extract city_end values
    end_cities = [m.eval(city_end[d]).as_long() for d in range(n_days)]

    # Build overlapped segments: if a flight occurs on day d (d>=2), then day d is included in both
    # the previous city's segment (as end) and the next city's segment (as start).
    boundaries = []
    for d in range(1, n_days):  # day 2..16 in 1-based indexing
        if m.eval(city_end[d] != city_end[d - 1]).is_true():
            boundaries.append(d + 1 - 1)  # keep as 1-based day index; here d is zero-based index for day number-1

    # Convert zero-based boundary indices to 1-based day numbers
    # Above we constructed boundaries as zero-based; convert to 1-based for human-readable day numbers
    boundaries = [b + 1 for b in boundaries]  # days where a flight happens (1-based), between day b-1 and b in end_cities

    segments = []
    if not boundaries:
        segments.append({
            "day_range": f"Day 1-16",
            "place": cities[end_cities[0]]
        })
    else:
        # First segment: Day 1 to first boundary (inclusive)
        first_city = end_cities[0]
        segments.append({
            "day_range": f"Day 1-{boundaries[0]}",
            "place": cities[first_city]
        })
        # Middle segments: from boundary i to boundary i+1
        for i in range(len(boundaries) - 1):
            b = boundaries[i]
            next_b = boundaries[i + 1]
            city_at_b = end_cities[b - 1]  # end of day b is city_at_b
            segments.append({
                "day_range": f"Day {b}-{next_b}",
                "place": cities[city_at_b]
            })
        # Last segment: from last boundary to day 16
        last_b = boundaries[-1]
        last_city = end_cities[last_b - 1]
        segments.append({
            "day_range": f"Day {last_b}-16",
            "place": cities[last_city]
        })

    print(json.dumps({"itinerary": segments}, ensure_ascii=False))

if __name__ == "__main__":
    main()
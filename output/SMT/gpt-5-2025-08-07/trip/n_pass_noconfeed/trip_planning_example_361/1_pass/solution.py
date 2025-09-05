import json
from z3 import *

def solve_itinerary():
    # Input variables / parameters
    total_days = 15
    cities = ["Paris", "Madrid", "Bucharest", "Seville"]
    city_index = {name: i for i, name in enumerate(cities)}
    P, M, B, S = city_index["Paris"], city_index["Madrid"], city_index["Bucharest"], city_index["Seville"]

    # Required presence (including flight overlap rule)
    required_days = {
        P: 6,   # Paris
        M: 7,   # Madrid
        B: 2,   # Bucharest
        S: 3,   # Seville
    }

    # Direct flight connectivity (undirected graph)
    direct_pairs = set()
    def add_edge(a, b):
        direct_pairs.add((a, b))
        direct_pairs.add((b, a))

    add_edge(P, B)
    add_edge(S, P)
    add_edge(M, B)
    add_edge(M, P)
    add_edge(M, S)

    # Event constraints:
    # - Attend show in Madrid on days 1..7 (inclusive)
    show_city = M
    show_start_day = 1
    show_end_day = 7

    # - Visit Bucharest on days 14 and 15 (inclusive)
    must_be_in_B_days = [14, 15]

    # Derived: number of flight days = sum(required_days) - total_days
    flights_needed = sum(required_days.values()) - total_days
    assert flights_needed >= 0, "Overlaps cannot be negative; check inputs."

    # Z3 variables: for each day d (1..total_days), we define start_city[d], end_city[d]
    # start_city[d] is the city at the beginning of day d
    # end_city[d] is the city at the end of day d (after any flight on day d)
    # If start_city[d] != end_city[d], then a direct flight occurs on day d and both cities count for that day.
    start_city = [Int(f"start_{d+1}") for d in range(total_days)]
    end_city = [Int(f"end_{d+1}") for d in range(total_days)]

    s = Solver()

    # Domain constraints
    for d in range(total_days):
        s.add(And(start_city[d] >= 0, start_city[d] < len(cities)))
        s.add(And(end_city[d] >= 0, end_city[d] < len(cities)))

    # Continuity: end of day d is the start of day d+1
    for d in range(total_days - 1):
        s.add(start_city[d + 1] == end_city[d])

    # Direct flight rule: if start != end on day d, must be a direct connection
    for d in range(total_days):
        # Allowed if no flight (start == end) or if (start, end) is in direct_pairs
        allowed_edges = [And(start_city[d] == a, end_city[d] == b) for (a, b) in direct_pairs]
        s.add(Or(start_city[d] == end_city[d], Or(*allowed_edges)))

    # Presence and counts
    # present[d][c] = 1 if (start[d] == c or end[d] == c), else 0
    def present_expr(d, c):
        return If(Or(start_city[d] == c, end_city[d] == c), 1, 0)

    # Enforce exact required presence days for each city
    for c in range(len(cities)):
        s.add(Sum([present_expr(d, c) for d in range(total_days)]) == required_days[c])

    # Show attendance: must be in Madrid on each day 1..7
    for day in range(show_start_day, show_end_day + 1):
        idx = day - 1
        s.add(Or(start_city[idx] == show_city, end_city[idx] == show_city))

    # Bucharest on days 14 and 15
    for day in must_be_in_B_days:
        idx = day - 1
        s.add(Or(start_city[idx] == B, end_city[idx] == B))

    # Ensure total number of flight days is exactly flights_needed
    flights = [If(start_city[d] != end_city[d], 1, 0) for d in range(total_days)]
    s.add(Sum(flights) == flights_needed)

    # Solve
    if s.check() != sat:
        # As a fallback (shouldn't happen with current constraints), emit an empty itinerary
        return {"itinerary": []}

    m = s.model()

    # Extract solution
    start_vals = [m.evaluate(start_city[d]).as_long() for d in range(total_days)]
    end_vals = [m.evaluate(end_city[d]).as_long() for d in range(total_days)]

    # Build a day-by-day itinerary.
    # For travel days, show both origin and destination on that day (e.g., "Madrid and Seville").
    itinerary = []
    for d in range(total_days):
        sc = start_vals[d]
        ec = end_vals[d]
        if sc == ec:
            place = cities[sc]
        else:
            place = f"{cities[sc]} and {cities[ec]}"
        itinerary.append({"day_range": f"Day {d+1}", "place": place})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False))
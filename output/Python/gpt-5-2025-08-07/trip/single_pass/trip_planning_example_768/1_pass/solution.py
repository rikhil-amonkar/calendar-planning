import json
from typing import List, Tuple, Optional

def plan_trip():
    # Input variables (constraints)
    total_days = 16
    cities = ["Mykonos", "London", "Copenhagen", "Tallinn", "Oslo", "Nice"]
    required_days = {
        "Mykonos": 4,
        "Nice": 3,
        "London": 2,
        "Copenhagen": 3,
        "Oslo": 5,
        "Tallinn": 4,
    }
    # Direct flight pairs (bidirectional)
    direct_flights = [
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
    conference_nice_days = {14, 16}   # Must be in Nice
    friend_oslo_range = (10, 14)      # Must be in Oslo at least one day within this range (inclusive)

    # Derived values
    city_to_idx = {c: i for i, c in enumerate(cities)}
    idx_to_city = {i: c for c, i in city_to_idx.items()}
    R = [required_days[c] for c in cities]
    sum_required = sum(R)
    flights_needed = sum_required - total_days  # Number of flight days needed so city-day counts match
    if flights_needed < 0:
        raise ValueError("Infeasible: sum of required days less than total days.")
    # Build adjacency (undirected)
    adj = {city_to_idx[c]: set() for c in cities}
    for a, b in direct_flights:
        ai, bi = city_to_idx[a], city_to_idx[b]
        adj[ai].add(bi)
        adj[bi].add(ai)

    # Helper functions
    def in_oslo_range(day_idx):
        return friend_oslo_range[0] <= day_idx <= friend_oslo_range[1]

    # DFS state:
    best_schedule: Optional[List[Tuple[int, Optional[int]]]] = None  # per day: (start_city_idx, dest_city_idx or None)
    n = total_days

    # Order start candidates (heuristic; still general)
    start_candidates = ["Mykonos", "London", "Copenhagen", "Tallinn", "Oslo", "Nice"]
    start_order = [city_to_idx[c] for c in start_candidates if c in city_to_idx]

    # Precompute an order of neighbors to try: prioritize those with higher remaining requirements (dynamic)
    def neighbor_order(current, counts):
        # Return neighbors sorted by remaining needed (desc), then by a deterministic name order
        rem_needed = [R[i] - counts[i] for i in range(len(cities))]
        neighbors = list(adj[current])
        neighbors.sort(key=lambda x: (-rem_needed[x], cities[x]))
        return neighbors

    # Core DFS
    def dfs(day, start_city, flights_used, counts, visited, schedule, met_oslo):
        nonlocal best_schedule

        # Prune if already found solution
        if best_schedule is not None:
            return

        # Remaining days and flights
        days_left = n - day + 1
        flights_left = flights_needed - flights_used

        # Basic feasibility checks
        if flights_left < 0:
            return
        if flights_left > days_left:
            return
        # Cannot visit all cities if too few flights remain to add new cities (each flight can add at most one new city)
        if len(visited) + flights_left < len(cities):
            return
        # Upper bound prune: each city can get at most one count per remaining day
        for i in range(len(cities)):
            if counts[i] > R[i]:
                return
            if counts[i] + days_left < R[i]:
                return

        # If finalized all days, validate
        if day > n:
            if flights_used != flights_needed:
                return
            # All city counts match
            if any(counts[i] != R[i] for i in range(len(cities))):
                return
            # Must be in Nice on specific conference days (already enforced during assignment, but double-check)
            for d in conference_nice_days:
                sc, dest = schedule[d - 1]
                if not (sc == city_to_idx["Nice"] or dest == city_to_idx["Nice"]):
                    return
            # Visit all cities
            if len(visited) != len(cities):
                return
            # Met friend in Oslo within the specified range
            if not met_oslo:
                return
            best_schedule = schedule[:]
            return

        sc = start_city
        nice_idx = city_to_idx["Nice"]
        oslo_idx = city_to_idx["Oslo"]

        # Try "no flight" option if possible
        must_include_nice_today = (day in conference_nice_days)
        # If we must be in Nice today and we are not starting in Nice, we cannot choose no-flight
        if not (must_include_nice_today and sc != nice_idx):
            # Apply no-flight
            counts_nf = counts[:]
            counts_nf[sc] += 1
            # Quick prune if exceeding
            if counts_nf[sc] <= R[sc]:
                schedule[day - 1] = (sc, None)
                visited_nf = set(visited)
                visited_nf.add(sc)
                met_nf = met_oslo or (in_oslo_range(day) and sc == oslo_idx)
                dfs(day + 1, sc, flights_used, counts_nf, visited_nf, schedule, met_nf)

        # Try "flight" options
        if flights_used < flights_needed:
            # Neighbors ordered by remaining requirement
            for dest in neighbor_order(sc, counts):
                # If today must include Nice and we don't start in Nice, destination must be Nice
                if must_include_nice_today and sc != nice_idx and dest != nice_idx:
                    continue
                counts_f = counts[:]
                counts_f[sc] += 1
                counts_f[dest] += 1
                # If any count exceeds requirement, skip
                if counts_f[sc] > R[sc] or counts_f[dest] > R[dest]:
                    continue
                schedule[day - 1] = (sc, dest)
                visited_f = set(visited)
                visited_f.add(sc)
                visited_f.add(dest)
                met_f = met_oslo or (in_oslo_range(day) and (sc == oslo_idx or dest == oslo_idx))
                dfs(day + 1, dest, flights_used + 1, counts_f, visited_f, schedule, met_f)

    # Attempt with different starting cities
    for start_city in start_order:
        counts0 = [0] * len(cities)
        visited0 = set()
        schedule0: List[Tuple[int, Optional[int]]] = [(0, None)] * n
        # Early feasibility: ensure it's possible to include Nice on conference days from this start path
        dfs(1, start_city, 0, counts0, visited0, schedule0, False)
        if best_schedule is not None:
            break

    if best_schedule is None:
        raise RuntimeError("No feasible itinerary found with given constraints.")

    # Build overlapping segments for output
    # schedule is per-day: (start_city, dest_or_none)
    start_cities = [best_schedule[i][0] for i in range(n)]
    segments = []
    seg_city = start_cities[0]
    seg_start = 1
    for i in range(2, n + 1):
        if start_cities[i - 1] != start_cities[i - 2]:
            # Flight occurred on day i-1
            end_prev = i - 1
            segments.append({"day_range": f"Day {seg_start}-{end_prev}", "place": idx_to_city[seg_city]})
            seg_city = start_cities[i - 1]
            seg_start = i - 1
    # Final base segment
    segments.append({"day_range": f"Day {seg_start}-{n}", "place": idx_to_city[seg_city]})
    # If there is a flight on the last day, add arrival city day 16-16 as per rule
    if best_schedule[n - 1][1] is not None:
        last_dest = best_schedule[n - 1][1]
        segments.append({"day_range": f"Day {n}-{n}", "place": idx_to_city[last_dest]})

    return {"itinerary": segments}

if __name__ == "__main__":
    result = plan_trip()
    print(json.dumps(result, ensure_ascii=False))
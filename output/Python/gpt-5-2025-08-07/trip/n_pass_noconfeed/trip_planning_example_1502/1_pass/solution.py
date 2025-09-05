import json
from collections import defaultdict

def build_adjacency(cities, undirected_edges, directed_edges):
    adj = defaultdict(set)
    for a, b in undirected_edges:
        adj[a].add(b)
        adj[b].add(a)
    for a, b in directed_edges:
        adj[a].add(b)
    # Ensure all cities appear in adjacency even if isolated
    for c in cities:
        adj[c] = adj[c]  # touch to create key
    return adj

def compute_fixed_starts(durations, event_windows):
    fixed_starts = {}
    for city, window in event_windows.items():
        if city in durations and window is not None:
            start, end = window
            if (end - start + 1) == durations[city]:
                fixed_starts[city] = start
    return fixed_starts

def validate_event_coverage(assignments, durations, event_windows):
    # Ensure each event window is entirely covered by city's stay
    for city, window in event_windows.items():
        if window is None:
            continue
        if city not in assignments:
            return False
        s = assignments[city]
        e = s + durations[city] - 1
        ws, we = window
        if not (s <= ws and e >= we):
            return False
    return True

def backtrack_path(cities, durations, adj, fixed_starts, total_days):
    n = len(cities)
    all_cities = set(cities)

    # Pre-calc: total end day if all cities used with start at day 1
    # end_day = 1 + sum(durations) - (n)
    # Here we just use this to ensure total_days matches expectation
    expected_end = 1 + sum(durations[c] for c in cities) - n
    if expected_end != total_days:
        # Infeasible by arithmetic relation
        return None, None

    # Candidate starting cities: either fixed_start == 1 or no fixed start
    start_candidates = []
    for c in cities:
        fs = fixed_starts.get(c)
        if fs is None or fs == 1:
            start_candidates.append(c)

    # Sort for determinism
    start_candidates.sort()

    best_path = None
    best_assign = None

    def dfs(path, assigned_start):
        nonlocal best_path, best_assign
        if len(path) == n:
            # Completed all cities, check end day equals total_days
            last = path[-1]
            end_day = assigned_start[last] + durations[last] - 1
            if end_day == total_days:
                best_path = list(path)
                best_assign = dict(assigned_start)
                return True
            return False

        last_city = path[-1]
        s_last = assigned_start[last_city]
        e_last = s_last + durations[last_city] - 1
        s_next = e_last

        remaining = all_cities - set(path)

        # Forced next city if any remaining has fixed start equal to s_next
        forced = [c for c in remaining if fixed_starts.get(c) == s_next]
        if len(forced) > 1:
            return False  # impossible: two cities both must start same day
        # Build candidate neighbors
        candidates = [c for c in adj[last_city] if c in remaining]
        # Filter by fixed start compatibility (if city has fixed start, must match s_next)
        cand2 = []
        for c in candidates:
            fs = fixed_starts.get(c)
            if fs is None or fs == s_next:
                cand2.append(c)
        candidates = cand2

        # If a forced city exists, narrow to it
        if len(forced) == 1:
            forced_city = forced[0]
            if forced_city not in candidates:
                return False
            candidates = [forced_city]

        # Heuristic: sort candidates to keep determinism
        candidates.sort()

        for c in candidates:
            # Assign start day
            assigned_start[c] = s_next
            path.append(c)

            # Early pruning: if this is the last city, check total end day now
            if len(path) == n:
                last = path[-1]
                end_day = assigned_start[last] + durations[last] - 1
                if end_day != total_days:
                    path.pop()
                    assigned_start.pop(c, None)
                    continue

            if dfs(path, assigned_start):
                return True

            # backtrack
            path.pop()
            assigned_start.pop(c, None)

        return False

    # Try each possible start
    for start_city in start_candidates:
        # If start_city has fixed start and it's not 1, skip
        fs = fixed_starts.get(start_city)
        if fs is not None and fs != 1:
            continue

        # Additionally, if there exists some city with fixed start 3 (e.g., Vienna),
        # ensure start_city duration allows next start to be that fixed start
        # This is naturally enforced via recursion with forced next start,
        # but we can keep it as is.

        assigned_start = {start_city: 1}
        if dfs([start_city], assigned_start):
            return best_path, best_assign

    return None, None

def main():
    total_days = 27

    # Define cities and durations (days in each city)
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
        "Frankfurt": 4,
    }
    cities = list(durations.keys())

    # Event windows (inclusive): if equals duration, implies fixed start
    event_windows = {
        "Vienna": (3, 6),     # wedding between day 3 and 6
        "Madrid": (6, 7),     # show on days 6-7
        "Krakow": (11, 15),   # meet friends between day 11 and 15
        "Riga": (20, 23),     # conference during day 20-23
        "Tallinn": (23, 27),  # workshop between day 23 and 27
        # Others have no fixed windows
        "Santorini": None,
        "Valencia": None,
        "Seville": None,
        "Bucharest": None,
        "Frankfurt": None,
    }

    # Direct flights: undirected "and", directed "from A to B"
    undirected_edges = [
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
        ("Frankfurt", "Bucharest"),
        ("Madrid", "Bucharest"),
        ("Frankfurt", "Riga"),
        ("Frankfurt", "Tallinn"),
        ("Madrid", "Frankfurt"),
    ]
    directed_edges = [
        ("Riga", "Tallinn"),
    ]

    adj = build_adjacency(cities, undirected_edges, directed_edges)

    fixed_starts = compute_fixed_starts(durations, event_windows)

    path, assignments = backtrack_path(cities, durations, adj, fixed_starts, total_days)

    if path is None or assignments is None:
        # If no solution found, output empty itinerary (should not happen with given constraints)
        print(json.dumps({"itinerary": []}))
        return

    # Final validation: ensure event windows are fully covered
    if not validate_event_coverage(assignments, durations, event_windows):
        print(json.dumps({"itinerary": []}))
        return

    # Build itinerary output sorted by start day
    items = []
    for city in path:
        s = assignments[city]
        e = s + durations[city] - 1
        items.append((s, e, city))

    # Sort by start day for clarity
    items.sort(key=lambda x: x[0])

    itinerary = []
    for s, e, city in items:
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
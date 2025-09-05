import json
from collections import defaultdict

def build_adjacency(edges):
    adj = defaultdict(set)
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    return adj

def compute_itinerary(cities, durations, windows, edges, total_days):
    # Basic validation
    n = len(cities)
    total_city_days = sum(durations[c] for c in cities)
    if total_city_days - (n - 1) != total_days:
        raise ValueError("Inconsistent durations vs total days with overlap logic.")
    adj = build_adjacency(edges)

    # Backtracking search
    best_sequence = []
    best_intervals = {}

    # Determine initial next start day
    S0 = 1

    # For pruning: required starts
    required_starts = {c: w[0] for c, w in windows.items()}
    required_ends = {c: w[1] for c, w in windows.items()}

    def backtrack(sequence, intervals, next_start, remaining):
        nonlocal best_sequence, best_intervals

        # Prune: if we've passed any required start for a not-yet-placed city
        for c, rs in required_starts.items():
            if c in sequence:
                continue
            if next_start > rs:
                return

        if not remaining:
            # All placed, verify last end equals total_days
            if sequence:
                last_city = sequence[-1]
                _, last_end = intervals[last_city]
                if last_end == total_days:
                    best_sequence = sequence[:]
                    best_intervals = intervals.copy()
            return

        # Candidates must connect to previous city (if any)
        prev_city = sequence[-1] if sequence else None

        # Build candidate list
        candidates = []
        for c in remaining:
            if prev_city is not None and c not in adj[prev_city]:
                continue
            # Window check for candidate
            d = durations[c]
            start = next_start
            end = start + d - 1
            if c in windows:
                rs, re = windows[c]
                if start != rs or end != re:
                    continue
            candidates.append(c)

        # Prefer candidates whose required start equals this start (deterministic and prunes faster)
        candidates.sort(key=lambda x: (0 if (x in windows and windows[x][0] == next_start) else 1, x))

        for c in candidates:
            d = durations[c]
            start = next_start
            end = start + d - 1
            new_intervals = intervals.copy()
            new_intervals[c] = (start, end)

            new_sequence = sequence + [c]
            new_remaining = [r for r in remaining if r != c]
            new_next_start = end  # Overlap day rule

            # Additional sanity: if we've placed all but one city and the last city has a window, ensure feasibility
            # (Not strictly necessary due to the earlier prune, but harmless.)

            backtrack(new_sequence, new_intervals, new_next_start, new_remaining)
            if best_sequence:
                return  # Found a valid solution; stop at first valid

    # Prepare data structures for search
    remaining_cities = cities[:]

    # Start backtracking
    backtrack([], {}, S0, remaining_cities)

    if not best_sequence:
        return {"itinerary": []}

    # Build JSON itinerary
    itinerary = []
    for c in best_sequence:
        s, e = best_intervals[c]
        itinerary.append({"day_range": f"Day {s}-{e}", "place": c})

    return {"itinerary": itinerary}

def main():
    # Input variables (constraints)
    total_days = 19
    cities = [
        "Lisbon",
        "Dubrovnik",
        "Copenhagen",
        "Prague",
        "Tallinn",
        "Stockholm",
        "Split",
        "Lyon",
    ]
    durations = {
        "Lisbon": 2,
        "Dubrovnik": 5,
        "Copenhagen": 5,
        "Prague": 3,
        "Tallinn": 2,
        "Stockholm": 4,
        "Split": 3,
        "Lyon": 2,
    }
    # Required presence windows (inclusive)
    windows = {
        "Tallinn": (1, 2),       # meet friend between day 1 and day 2
        "Lisbon": (4, 5),        # workshop between day 4 and day 5
        "Stockholm": (13, 16),   # wedding between day 13 and day 16
        "Lyon": (18, 19),        # annual show between day 18 and day 19
    }
    # Direct flights (undirected)
    edges = [
        ("Dubrovnik", "Stockholm"),
        ("Lisbon", "Copenhagen"),
        ("Lisbon", "Lyon"),
        ("Copenhagen", "Stockholm"),
        ("Copenhagen", "Split"),
        ("Prague", "Stockholm"),
        ("Tallinn", "Stockholm"),
        ("Prague", "Lyon"),
        ("Lisbon", "Stockholm"),
        ("Prague", "Lisbon"),
        ("Stockholm", "Split"),
        ("Prague", "Copenhagen"),
        ("Split", "Lyon"),
        ("Copenhagen", "Dubrovnik"),
        ("Prague", "Split"),
        ("Tallinn", "Copenhagen"),
        ("Tallinn", "Prague"),
    ]

    result = compute_itinerary(cities, durations, windows, edges, total_days)
    print(json.dumps(result))

if __name__ == "__main__":
    main()
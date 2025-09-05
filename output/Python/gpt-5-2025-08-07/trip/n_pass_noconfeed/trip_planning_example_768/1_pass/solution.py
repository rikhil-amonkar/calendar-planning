import itertools
import json
from collections import defaultdict

def main():
    # Input variables (trip constraints)
    total_days = 16
    required_days = {
        "Mykonos": 4,
        "Nice": 3,
        "London": 2,
        "Copenhagen": 3,
        "Oslo": 5,
        "Tallinn": 4,
    }
    cities = list(required_days.keys())

    # Direct flight pairs (undirected)
    direct_flights_pairs = [
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

    # Build adjacency
    neighbors = defaultdict(set)
    for a, b in direct_flights_pairs:
        neighbors[a].add(b)
        neighbors[b].add(a)

    # Conference constraints
    conference_city = "Nice"
    conference_days = {14, 16}

    # Friend meeting constraints
    friend_city = "Oslo"
    friend_window = (10, 14)  # inclusive

    # Helper: check adjacency
    def is_adjacent(a, b):
        return b in neighbors[a]

    # Generate Hamiltonian paths ending in conference_city
    other_cities = [c for c in cities if c != conference_city]

    # Prefer starting from Mykonos if available to reflect user's preference
    # but still algorithmically search all valid options
    def start_priority(seq):
        # Score sequences: earlier Mykonos, and Oslo right before Nice
        score = 0
        if seq[0] == "Mykonos":
            score -= 10
        if len(seq) >= 2 and seq[-1] == conference_city and seq[-2] == friend_city:
            score -= 5
        return score

    def dfs_paths(start):
        # DFS to build paths that use each city exactly once and end in conference_city
        stack = [(start, [start])]
        visited_all = set(cities)
        results = []

        while stack:
            current, path = stack.pop()
            if len(path) == len(cities):
                if path[-1] == conference_city:
                    results.append(path)
                continue

            for nxt in sorted(neighbors[current]):
                if nxt in path:
                    continue
                # Only allow conference city at the very end
                if nxt == conference_city and len(path) != len(cities) - 1:
                    continue
                # Must be one of our cities
                if nxt not in visited_all:
                    continue
                stack.append((nxt, path + [nxt]))
        # Sort results by heuristic for stability
        results.sort(key=start_priority)
        return results

    # Compute assigned day lengths:
    # For every city except the last (which is conference_city), assigned_len = required - 1
    # Because departure flight day counts for both origin and destination.
    def assigned_lengths_for_sequence(seq):
        lengths = {}
        for city in seq[:-1]:
            lengths[city] = required_days[city] - 1
        last = seq[-1]
        lengths[last] = required_days[last]
        return lengths

    # Build full assigned schedule (each day assigned to exactly one city)
    def build_assigned_schedule(seq, lengths):
        day = 1
        assigned_ranges = {}
        for city in seq:
            L = lengths[city]
            start = day
            end = day + L - 1
            assigned_ranges[city] = (start, end)
            day = end + 1
        return assigned_ranges

    # Compute occupancy including flight days for origin cities
    def compute_occupancy(seq, assigned_ranges):
        occupancy = {c: set() for c in seq}
        # Add assigned days
        for c, (s, e) in assigned_ranges.items():
            for d in range(s, e + 1):
                occupancy[c].add(d)
        # Add flight days to origin city (departure day is end_assigned(origin) + 1)
        for i in range(len(seq) - 1):
            origin = seq[i]
            dep_day = assigned_ranges[origin][1] + 1
            occupancy[origin].add(dep_day)
        return occupancy

    def validate(seq):
        # Check adjacency across the path
        if not all(is_adjacent(seq[i], seq[i + 1]) for i in range(len(seq) - 1)):
            return None

        lengths = assigned_lengths_for_sequence(seq)
        # Sum of assigned lengths must match total days
        if sum(lengths.values()) != total_days:
            return None

        assigned_ranges = build_assigned_schedule(seq, lengths)

        # Ensure conference city occupies the required days
        conf_start, conf_end = assigned_ranges[conference_city]
        for d in conference_days:
            if not (conf_start <= d <= conf_end):
                return None

        # Compute occupancy sets
        occupancy = compute_occupancy(seq, assigned_ranges)

        # Check each city's required days match occupancy count
        for city in seq:
            if len(occupancy[city]) != required_days[city]:
                return None

        # Friend meeting window check
        window_days = set(range(friend_window[0], friend_window[1] + 1))
        if occupancy[friend_city].isdisjoint(window_days):
            return None

        return assigned_ranges

    # Try all starting points (prefer Mykonos if present)
    starts = sorted(other_cities, key=lambda c: (c != "Mykonos", c))

    valid_itinerary = None
    for start in starts:
        for path in dfs_paths(start):
            ranges = validate(path)
            if ranges is not None:
                # Build output itinerary from assigned ranges in the order of the path
                itinerary = []
                for city in path:
                    s, e = ranges[city]
                    itinerary.append({
                        "day_range": f"Day {s}-{e}",
                        "place": city
                    })
                valid_itinerary = itinerary
                break
        if valid_itinerary:
            break

    # Fallback if not found (should not happen with given constraints)
    if not valid_itinerary:
        output = {"itinerary": []}
    else:
        output = {"itinerary": valid_itinerary}

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()
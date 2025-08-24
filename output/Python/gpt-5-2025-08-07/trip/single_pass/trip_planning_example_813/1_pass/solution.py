import json
from itertools import permutations

def build_adjacency(edges):
    adj = {}
    for a, b in edges:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def compute_ranges(path, desired_days, total_days):
    # Given a path and desired per-city durations (with overlap on transition days),
    # compute the inclusive day ranges for each city and ensure total days match.
    ranges = {}
    prev_end = 0
    for i, city in enumerate(path):
        dur = desired_days[city]
        if i == 0:
            start = 1
            end = dur
        else:
            start = prev_end  # overlap day with previous city
            end = prev_end + dur - 1
        ranges[city] = (start, end)
        prev_end = end
    if prev_end != total_days:
        return None  # invalid mapping
    return ranges

def find_hamiltonian_paths_with_constraints(adj, cities, start, end, must_adjacent_order=("Stuttgart", "London")):
    n = len(cities)
    all_paths = []

    def dfs(path, visited):
        current = path[-1]
        if len(path) == n:
            # Must end at the specified endpoint
            if current == end:
                # Validate adjacency constraint if both present
                if must_adjacent_order[0] in path and must_adjacent_order[1] in path:
                    i = path.index(must_adjacent_order[0])
                    j = path.index(must_adjacent_order[1])
                    if j != i + 1:
                        return
                all_paths.append(path[:])
            return

        # Prune: if London appears before Stuttgart, invalid (must be Stuttgart immediately followed by London)
        if must_adjacent_order[1] in path and must_adjacent_order[0] not in path:
            return

        # If Stuttgart is last in path and London not yet in path, force next city to be London (if possible)
        force_next = None
        if path[-1] == must_adjacent_order[0] and must_adjacent_order[1] not in path:
            force_next = must_adjacent_order[1]

        # Try neighbors
        for nb in sorted(adj[current]):
            if nb in visited:
                continue
            # If last step (to complete path), must go to the designated end
            if len(path) == n - 1 and nb != end:
                continue
            # If a forced next city is required (to keep Stuttgart immediately before London)
            if force_next is not None and nb != force_next:
                continue
            path.append(nb)
            visited.add(nb)
            # Additional prune: if both Stuttgart and London already in path, enforce adjacency immediately
            if must_adjacent_order[0] in path and must_adjacent_order[1] in path:
                i = path.index(must_adjacent_order[0])
                j = path.index(must_adjacent_order[1])
                if j != i + 1:
                    visited.remove(nb)
                    path.pop()
                    continue
            dfs(path, visited)
            visited.remove(nb)
            path.pop()

    dfs([start], {start})
    return all_paths

def main():
    # Input variables (trip constraints)
    total_days = 17
    desired_days = {
        "Seville": 5,
        "Vilnius": 3,
        "Santorini": 2,
        "London": 2,
        "Stuttgart": 3,
        "Dublin": 3,
        "Frankfurt": 5,
    }
    # Direct flights (undirected edges)
    flight_pairs = [
        ("Frankfurt", "Dublin"),
        ("Frankfurt", "London"),
        ("London", "Dublin"),
        ("Vilnius", "Frankfurt"),
        ("Frankfurt", "Stuttgart"),
        ("Dublin", "Seville"),
        ("London", "Santorini"),
        ("Stuttgart", "London"),
        ("Santorini", "Dublin"),
    ]

    # Special constraints
    stuttgart_window = (7, 9)  # must be in Stuttgart between day 7 and 9 (inclusive)
    london_meet_window = (9, 10)  # meet friends in London between day 9 and 10 (inclusive)

    # Build adjacency
    adj = build_adjacency(flight_pairs)
    cities = list(desired_days.keys())

    # Basic feasibility checks
    if sum(desired_days.values()) != total_days + (len(cities) - 1):
        raise ValueError("Desired days must equal total_days + number_of_flights (cities-1) due to overlap rule.")

    # Endpoints detection (degree-1 nodes)
    endpoints = [c for c in cities if len(adj.get(c, [])) == 1]
    if len(endpoints) != 2:
        raise ValueError("Graph must have exactly two endpoints to form a single path visiting all cities once.")
    # We expect endpoints to include Seville and Vilnius based on constraints
    if set(endpoints) != {"Seville", "Vilnius"}:
        raise ValueError("Unexpected endpoints; expected Seville and Vilnius.")

    # Generate Hamiltonian paths starting/ending at the endpoints with Stuttgart->London adjacency constraint
    solutions = []
    for start in endpoints:
        end = [e for e in endpoints if e != start][0]
        paths = find_hamiltonian_paths_with_constraints(adj, cities, start, end, must_adjacent_order=("Stuttgart", "London"))
        for path in paths:
            ranges = compute_ranges(path, desired_days, total_days)
            if not ranges:
                continue
            # Check Stuttgart window exactly matches 7-9
            if ranges["Stuttgart"] != stuttgart_window:
                continue
            # Check London covers both day 9 and 10 and duration is 2 (implied by desired_days)
            lon_start, lon_end = ranges["London"]
            if not (lon_start <= london_meet_window[0] <= lon_end and lon_start <= london_meet_window[1] <= lon_end):
                continue
            # All constraints met
            solutions.append((path, ranges))

    if not solutions:
        raise ValueError("No feasible itinerary found under the given constraints.")

    # Choose the first feasible solution (could implement selection criteria if multiple)
    path, ranges = solutions[0]

    # Build itinerary output
    itinerary = []
    for city in path:
        start, end = ranges[city]
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    result = {"itinerary": itinerary}
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()
import json
from typing import Dict, List, Tuple, Optional

def build_graph(cities: List[str]) -> Dict[str, set]:
    # Initialize adjacency sets
    adj = {c: set() for c in cities}
    # Given direct flights:
    undirected_pairs = [
        ("Copenhagen", "Athens"),
        ("Copenhagen", "Dubrovnik"),
        ("Munich", "Tallinn"),
        ("Copenhagen", "Munich"),
        ("Venice", "Munich"),
        ("Athens", "Dubrovnik"),
        ("Venice", "Athens"),
        ("Lyon", "Barcelona"),
        ("Copenhagen", "Reykjavik"),
        ("Reykjavik", "Munich"),
        ("Athens", "Munich"),
        ("Lyon", "Munich"),
        ("Barcelona", "Reykjavik"),
        ("Venice", "Copenhagen"),
        ("Barcelona", "Dubrovnik"),
        ("Lyon", "Venice"),
        ("Dubrovnik", "Munich"),
        ("Barcelona", "Athens"),
        ("Copenhagen", "Barcelona"),
        ("Venice", "Barcelona"),
        ("Barcelona", "Munich"),
        ("Barcelona", "Tallinn"),
        ("Copenhagen", "Tallinn"),
    ]
    # Add undirected edges
    for a, b in undirected_pairs:
        adj[a].add(b)
        adj[b].add(a)
    # Add the one directional flight: from Reykjavik to Athens
    adj["Reykjavik"].add("Athens")
    return adj

def intersects(day_range: Tuple[int, int], window: Tuple[int, int]) -> bool:
    a, b = day_range
    c, d = window
    return not (b < c or a > d)

def compute_day_range_for_index(durations: Dict[str, int], path: List[str]) -> Tuple[int, int]:
    """
    Compute start and end day for the last city in 'path' given durations and
    the "same-day" travel overlap rule: next segment starts on the previous segment's end day.
    """
    if not path:
        raise ValueError("Path must have at least one city to compute range.")
    # Compute start/end cumulatively
    # For k-th city (1-based), end_k = sum(d[1..k]) - (k-1)
    # start_1 = 1; start_k = end_{k-1}
    k = len(path)
    total = sum(durations[path[i]] for i in range(k))
    end_k = total - (k - 1)
    if k == 1:
        start_k = 1
    else:
        # previous end
        prev_total = total - durations[path[-1]]
        end_prev = prev_total - (k - 2)
        start_k = end_prev
    return (start_k, end_k)

def find_itinerary(
    cities: List[str],
    durations: Dict[str, int],
    windows: Dict[str, Tuple[int, int]],
    total_days: int,
    graph: Dict[str, set],
    preference_order: List[str]
) -> Optional[List[Tuple[str, Tuple[int,int]]]]:
    n = len(cities)
    all_durations_sum = sum(durations[c] for c in cities)
    # Sanity check: with n cities, sum(durations) must equal total_days + (n-1) to fit perfectly with overlaps
    if all_durations_sum != total_days + (n - 1):
        # Not strictly required to enforce, but ensures perfect fit
        pass

    pref_index = {c: i for i, c in enumerate(preference_order)}

    def sorted_candidates(cands: List[str]) -> List[str]:
        return sorted(cands, key=lambda x: pref_index.get(x, len(preference_order)))

    best_solution = None

    def dfs(path: List[str], ranges: List[Tuple[int,int]], visited: set):
        nonlocal best_solution
        if best_solution is not None:
            return
        k = len(path)
        if k == n:
            # Verify ends exactly on total_days
            if ranges[-1][1] == total_days:
                # All windows for placed cities checked along the way
                best_solution = list(zip(path, ranges))
            return

        remaining = [c for c in cities if c not in visited]
        # Determine next candidates by adjacency (if not first city)
        if k == 0:
            candidates = remaining
        else:
            last = path[-1]
            candidates = [c for c in remaining if c in graph[last]]

        # Order candidates by preference to find a valid solution quickly
        for cand in sorted_candidates(candidates):
            # Place cand and compute its range
            new_path = path + [cand]
            start_c, end_c = compute_day_range_for_index(durations, new_path)
            # Early pruning: if start > total_days or end < 1 or end > total_days for non-final placements?
            # Not necessary because final end will be total_days, but ensure end does not exceed total_days for last placement
            # Windows check if any
            if cand in windows:
                if not intersects((start_c, end_c), windows[cand]):
                    continue
            # Also verify that for cities already placed, their windows were checked already
            new_ranges = ranges + [(start_c, end_c)]
            new_visited = visited | {cand}
            dfs(new_path, new_ranges, new_visited)

    dfs([], [], set())
    return best_solution

def main():
    # Input variables based on the prompt
    total_days = 26
    cities = [
        "Venice",
        "Barcelona",
        "Copenhagen",
        "Lyon",
        "Reykjavik",
        "Dubrovnik",
        "Athens",
        "Tallinn",
        "Munich",
    ]
    durations = {
        "Venice": 4,
        "Barcelona": 3,
        "Copenhagen": 4,
        "Lyon": 4,
        "Reykjavik": 4,
        "Dubrovnik": 5,
        "Athens": 2,
        "Tallinn": 5,
        "Munich": 3,
    }
    # Windows: must be in the city on at least one day within [start, end], inclusive
    windows = {
        "Barcelona": (10, 12),   # meet friend between day 10 and 12
        "Copenhagen": (7, 10),   # visit relatives between day 7 and 10
        "Dubrovnik": (16, 20),   # attend wedding between day 16 and 20
    }
    graph = build_graph(cities)

    # A preference order guiding DFS to a feasible solution quickly
    preference_order = [
        "Lyon",
        "Venice",
        "Copenhagen",
        "Barcelona",
        "Reykjavik",
        "Athens",
        "Dubrovnik",
        "Munich",
        "Tallinn",
    ]

    solution = find_itinerary(cities, durations, windows, total_days, graph, preference_order)
    if solution is None:
        # If no solution found, output empty itinerary per spec
        output = {"itinerary": []}
        print(json.dumps(output))
        return

    # Build the JSON itinerary
    itinerary = []
    for city, (start, end) in solution:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
import json
from collections import defaultdict
from itertools import permutations

def build_graph(direct_flights):
    graph = defaultdict(set)
    for a, b in direct_flights:
        graph[a].add(b)
        graph[b].add(a)
    return graph

def effective_length_of_sequence(seq, durations):
    if not seq:
        # Special case used only for "adjacent anchors" where L must be 1
        return 1
    return sum(durations[c] for c in seq) - (len(seq) - 1)

def search_segment(graph, durations, available, L, prev_anchor, next_anchor):
    """
    Find all ordered sequences of cities (subset of 'available') such that:
    - Effective length of the sequence is exactly L
    - If prev_anchor is not None, the first city must be a neighbor of prev_anchor
    - If next_anchor is not None, the last city must be a neighbor of next_anchor
    - Consecutive cities in the sequence must be connected by a direct flight
    Returns a list of sequences (each sequence is a list of city names).
    """
    results = []

    # If no cities are needed between anchors (i.e., L == 1), anchors must be directly connected
    if L == 1:
        if prev_anchor is None or next_anchor is None:
            return []
        if next_anchor in graph[prev_anchor]:
            results.append([])
        return results

    # Candidate start cities
    start_candidates = list(available)
    # If there is a previous anchor, the first city must be adjacent to it
    if prev_anchor is not None:
        start_candidates = [c for c in start_candidates if c in graph[prev_anchor]]

    # Recursive DFS to build sequences
    def dfs(path, used, sum_dur):
        k = len(path)
        partial_L = sum_dur - (k - 1)

        # Prune if partial exceeds target
        if partial_L > L:
            return

        # If we've hit the target effective length, check adjacency to next anchor
        if partial_L == L:
            last_city = path[-1]
            if next_anchor is None or next_anchor in graph[last_city]:
                results.append(path[:])
            return

        # Need to add more cities
        last_node = path[-1]
        # Next candidates must be available and adjacent to last_node
        for nxt in graph[last_node]:
            if nxt in used:
                continue
            # Only choose from available set
            if nxt not in available:
                continue
            # Add and continue
            used.add(nxt)
            path.append(nxt)
            dfs(path, used, sum_dur + durations[nxt])
            path.pop()
            used.remove(nxt)

    for start in sorted(start_candidates):
        used = set([start])
        dfs([start], used, durations[start])

    # To keep deterministic, sort results by (length, lexicographic)
    def seq_key(seq):
        return (len(seq), tuple(seq))
    results.sort(key=seq_key)
    return results

def compute_itinerary():
    total_days = 25

    # City durations (exact desired stay lengths)
    durations = {
        "Valencia": 2,
        "Oslo": 3,
        "Lyon": 4,
        "Prague": 3,
        "Paris": 4,
        "Nice": 4,
        "Seville": 5,
        "Tallinn": 2,
        "Mykonos": 5,
        "Lisbon": 2,
    }

    # Direct flights (undirected)
    direct_flights = [
        ("Lisbon", "Paris"),
        ("Lyon", "Nice"),
        ("Tallinn", "Oslo"),
        ("Prague", "Lyon"),
        ("Paris", "Oslo"),
        ("Lisbon", "Seville"),
        ("Prague", "Lisbon"),
        ("Oslo", "Nice"),
        ("Valencia", "Paris"),
        ("Valencia", "Lisbon"),
        ("Paris", "Nice"),
        ("Nice", "Mykonos"),
        ("Paris", "Lyon"),
        ("Valencia", "Lyon"),
        ("Prague", "Oslo"),
        ("Prague", "Paris"),
        ("Seville", "Paris"),
        ("Oslo", "Lyon"),
        ("Prague", "Valencia"),
        ("Lisbon", "Nice"),
        ("Lisbon", "Oslo"),
        ("Valencia", "Seville"),
        ("Lisbon", "Lyon"),
        ("Paris", "Tallinn"),
        ("Prague", "Tallinn")
    ]
    graph = build_graph(direct_flights)

    # Anchors: city must cover exactly this interval [start, end]
    anchors = {
        "Valencia": (3, 4),
        "Seville": (5, 9),
        "Oslo": (13, 15),
        "Mykonos": (21, 25),
    }

    # Validate anchors align with durations and total days
    for city, (s, e) in anchors.items():
        d = durations[city]
        if e - s + 1 != d:
            raise ValueError(f"Anchor window for {city} does not match its duration.")
    # Ensure the last anchor ends at the trip end
    last_anchor_city, (_, last_end) = sorted(anchors.items(), key=lambda x: x[1][0])[-1]
    if last_end != total_days:
        raise ValueError("Last anchor must end on the final trip day.")

    all_cities = list(durations.keys())

    # Sort anchors by start day
    ordered_anchors = sorted(anchors.items(), key=lambda x: x[1][0])

    # Build segments between anchors (including the leading segment before first anchor)
    segments = []
    # Leading segment: from Day 1 to first anchor start
    first_anchor_city, (fa_start, fa_end) = ordered_anchors[0]
    segments.append({
        "prev_anchor": None,
        "next_anchor": first_anchor_city,
        "target_L": fa_start,  # effective length from day 1 to fa_start inclusive
    })

    # Middle segments between consecutive anchors
    for i in range(len(ordered_anchors) - 1):
        city_i, (s_i, e_i) = ordered_anchors[i]
        city_j, (s_j, e_j) = ordered_anchors[i + 1]
        target_L = (s_j - e_i) + 1
        segments.append({
            "prev_anchor": city_i,
            "next_anchor": city_j,
            "target_L": target_L,
        })

    # No trailing segment because last anchor ends on total_days

    # Search sequences for each segment with backtracking across segments to ensure disjoint city usage
    anchor_cities = set(anchors.keys())
    available_global = set(all_cities) - anchor_cities

    segment_solutions_cache = {}
    def solve_segments(idx, available):
        if idx == len(segments):
            return []  # No more segments to assign, success

        key = (idx, tuple(sorted(available)))
        if key in segment_solutions_cache:
            cached = segment_solutions_cache[key]
            # Return deep copy to avoid accidental mutation
            return [seg[:] for seg in cached] if cached is not None else None

        seg = segments[idx]
        prev_anchor = seg["prev_anchor"]
        next_anchor = seg["next_anchor"]
        target_L = seg["target_L"]

        candidates = search_segment(graph, durations, available, target_L, prev_anchor, next_anchor)

        for seq in candidates:
            # Ensure seq uses only available
            seq_set = set(seq)
            if not seq_set.issubset(available):
                continue
            # Recurse to next segment
            remaining = available - seq_set
            rest = solve_segments(idx + 1, remaining)
            if rest is not None:
                solution = [seq] + rest
                segment_solutions_cache[key] = [s[:] for s in solution]
                return solution

        segment_solutions_cache[key] = None
        return None

    segment_sequences = solve_segments(0, available_global)
    if segment_sequences is None:
        raise RuntimeError("No feasible segment sequences found that satisfy constraints.")

    # Build full route: segment0 + anchor1 + segment1 + anchor2 + ... + last anchor
    route = []
    for i, (anchor_city, _) in enumerate(ordered_anchors):
        # Add preceding segment
        route.extend(segment_sequences[i])
        # Add anchor
        route.append(anchor_city)

    # Sanity checks:
    # - Route includes all cities exactly once
    if set(route) != set(all_cities) or len(route) != len(all_cities):
        raise RuntimeError("Route does not include all cities exactly once.")

    # - Consecutive cities are connected by direct flights
    for a, b in zip(route, route[1:]):
        if b not in graph[a]:
            raise RuntimeError(f"No direct flight between consecutive cities: {a} -> {b}")

    # Compute day ranges along the route
    itinerary = []
    current_day = 1
    for city in route:
        start_day = current_day
        end_day = start_day + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })
        # Overlap rule: next start is this end day
        current_day = end_day

    if itinerary[-1]["day_range"] != f"Day {total_days - durations[route[-1]] + 1}-{total_days}":
        # Not strictly needed, but keeps shape consistent
        pass

    # Validate anchors appear at correct days
    city_to_range = {item["place"]: item["day_range"] for item in itinerary}
    for city, (s, e) in anchors.items():
        dr = city_to_range[city]
        # Parse day range
        left, right = dr.replace("Day ", "").split("-")
        ss = int(left.strip())
        ee = int(right.strip())
        if ss != s or ee != e:
            raise RuntimeError(f"Anchor misaligned for {city}: expected {s}-{e}, got {ss}-{ee}")

    # Validate trip ends on total_days
    last_start, last_end = itinerary[-1]["day_range"].replace("Day ", "").split("-")
    if int(last_end) != total_days:
        raise RuntimeError(f"Trip does not end on Day {total_days}.")

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))
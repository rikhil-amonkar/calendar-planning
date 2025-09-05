import json
from typing import List, Dict, Set, Tuple, Optional

def build_adjacency() -> Dict[str, Set[str]]:
    # Bidirectional edges (both directions)
    bi_edges = [
        ("Warsaw", "Riga"),
        ("Warsaw", "Tallinn"),
        ("Copenhagen", "Helsinki"),
        ("Lyon", "Paris"),
        ("Copenhagen", "Warsaw"),
        ("Lyon", "Oslo"),
        ("Paris", "Oslo"),
        ("Paris", "Riga"),
        ("Krakow", "Helsinki"),
        ("Paris", "Tallinn"),
        ("Oslo", "Riga"),
        ("Krakow", "Warsaw"),
        ("Paris", "Helsinki"),
        ("Copenhagen", "Santorini"),
        ("Helsinki", "Warsaw"),
        ("Helsinki", "Riga"),
        ("Copenhagen", "Krakow"),
        ("Copenhagen", "Riga"),
        ("Paris", "Krakow"),
        ("Copenhagen", "Oslo"),
        ("Oslo", "Tallinn"),
        ("Oslo", "Helsinki"),
        ("Copenhagen", "Tallinn"),
        ("Oslo", "Krakow"),
        ("Helsinki", "Tallinn"),
        ("Paris", "Copenhagen"),
        ("Paris", "Warsaw"),
        ("Oslo", "Warsaw"),
    ]
    # Directed edges (one way)
    directed_edges = [
        ("Riga", "Tallinn"),
        ("Santorini", "Oslo"),
    ]
    adj: Dict[str, Set[str]] = {}
    def add_edge(a: str, b: str):
        if a not in adj:
            adj[a] = set()
        adj[a].add(b)
    for a, b in bi_edges:
        add_edge(a, b)
        add_edge(b, a)
    for a, b in directed_edges:
        add_edge(a, b)
    return adj

def compute_center(include_days: Optional[Set[int]], intersect_window: Optional[Tuple[int, int]]) -> Optional[float]:
    if include_days:
        return (min(include_days) + max(include_days)) / 2.0
    if intersect_window:
        return (intersect_window[0] + intersect_window[1]) / 2.0
    return None

def ranges_intersect(a_start: int, a_end: int, b_start: int, b_end: int) -> bool:
    return not (a_end < b_start or b_end < a_start)

def solve_itinerary():
    total_days = 25

    # City durations (exact days desired in each city)
    durations = {
        "Paris": 5,
        "Warsaw": 2,
        "Krakow": 2,
        "Tallinn": 2,
        "Riga": 2,
        "Copenhagen": 5,
        "Helsinki": 5,
        "Oslo": 5,
        "Santorini": 2,
        "Lyon": 4,
    }

    # Constraints:
    # Cities that must include these exact calendar days (subset of their stay)
    must_include_days: Dict[str, Set[int]] = {
        "Krakow": {17, 18},
        "Riga": {23, 24},
        "Santorini": {12, 13},
    }
    # Cities that must intersect these windows at least one day
    must_intersect_windows: Dict[str, Tuple[int, int]] = {
        "Paris": (4, 8),
        "Helsinki": (18, 22),
    }

    cities = list(durations.keys())
    n = len(cities)
    # Sanity: ensure total days result possible (sum(d) - (n-1) must equal total_days)
    if sum(durations.values()) - (n - 1) != total_days:
        raise ValueError("Inconsistent durations vs total days; cannot schedule exactly 25 days.")

    # Build adjacency (direct flights)
    adj = build_adjacency()

    # Precompute centers for heuristic ordering
    centers = {}
    for c in cities:
        centers[c] = compute_center(must_include_days.get(c), must_intersect_windows.get(c))

    # Helper to compute s,e given current path and candidate
    def compute_start_end(path: List[str], candidate: str) -> Tuple[int, int]:
        # s1 = 1; for i>1: s[i] = s[i-1] + d[i-1] - 1
        if not path:
            s = 1
        else:
            # compute e of last
            s_last = 1
            for i, city in enumerate(path):
                if i == 0:
                    s_i = 1
                else:
                    s_i = s_last + durations[path[i-1]] - 1
                s_last = s_i
            e_last = s_last + durations[path[-1]] - 1
            s = e_last  # next start equals previous end (shared flight day)
        e = s + durations[candidate] - 1
        return s, e

    # Check constraints for a city at computed range
    def city_constraints_ok(city: str, s: int, e: int) -> bool:
        # Must include exact days if specified
        if city in must_include_days:
            req = must_include_days[city]
            for day in req:
                if not (s <= day <= e):
                    return False
        # Must intersect a window if specified
        if city in must_intersect_windows:
            w_start, w_end = must_intersect_windows[city]
            if not ranges_intersect(s, e, w_start, w_end):
                return False
        return True

    # After full path, validate everything
    def validate_full(path: List[str]) -> bool:
        # adjacency and constraints already checked; ensure last day ends at 25
        # Compute final end
        s = 1
        for i, city in enumerate(path):
            if i > 0:
                s = s + durations[path[i-1]] - 1
            e = s + durations[city] - 1
        if e != total_days:
            return False
        # Ensure all must constraints
        timeline = {}
        # Build ranges
        s_running = 1
        for i, city in enumerate(path):
            if i == 0:
                s_city = 1
            else:
                s_city = s_running + durations[path[i-1]] - 1
            e_city = s_city + durations[city] - 1
            timeline[city] = (s_city, e_city)
            s_running = s_city
        # Directed edges
        for i in range(len(path) - 1):
            if path[i+1] not in adj.get(path[i], set()):
                return False
        # City-specific constraints
        for c, days in must_include_days.items():
            s_c, e_c = timeline[c]
            for d in days:
                if not (s_c <= d <= e_c):
                    return False
        for c, (ws, we) in must_intersect_windows.items():
            s_c, e_c = timeline[c]
            if not ranges_intersect(s_c, e_c, ws, we):
                return False
        return True

    best_solution: Optional[List[str]] = None

    # DFS with heuristics
    def dfs(path: List[str], used: Set[str]) -> bool:
        nonlocal best_solution
        if len(path) == n:
            if validate_full(path):
                best_solution = path.copy()
                return True
            return False

        # Compute next start for heuristic scoring
        if not path:
            next_start = 1
        else:
            # compute e of last
            s_last = 1
            for i, city in enumerate(path):
                if i == 0:
                    s_i = 1
                else:
                    s_i = s_last + durations[path[i-1]] - 1
                s_last = s_i
            next_start = s_last + durations[path[-1]] - 1

        # Candidates
        remaining = [c for c in cities if c not in used]

        # Adjacency pruning: if not first, must be reachable from last
        if path:
            prev = path[-1]
            remaining = [c for c in remaining if c in adj.get(prev, set())]

        # Early pruning: if first city cannot start at day 1 due to include windows impossible
        pruned_candidates = []
        for c in remaining:
            s, e = compute_start_end(path, c)
            if not city_constraints_ok(c, s, e):
                continue
            pruned_candidates.append(c)

        # Heuristic sort: by closeness of ideal start to next_start
        def candidate_score(c: str) -> float:
            center = centers.get(c)
            dur = durations[c]
            if center is None:
                # Put unconstrained cities after constrained ones by giving a moderate penalty
                return abs(next_start - 100.0) + dur * 0.01
            ideal_start = center - (dur - 1) / 2.0
            return abs(ideal_start - next_start) + (0.001 * dur)

        pruned_candidates.sort(key=candidate_score)

        for c in pruned_candidates:
            s, e = compute_start_end(path, c)
            # Place c
            path.append(c)
            used.add(c)
            # Optional forward-check: ensure that for each remaining city with must-include days,
            # at least one potential position remains (very light check skipped for simplicity).
            if dfs(path, used):
                return True
            used.remove(c)
            path.pop()
        return False

    # Run DFS
    dfs([], set())

    if not best_solution:
        raise RuntimeError("No feasible itinerary found under given constraints.")

    # Build output itinerary with day ranges
    itinerary = []
    s_running = 1
    for i, city in enumerate(best_solution):
        if i == 0:
            s_city = 1
        else:
            s_city = s_running + durations[best_solution[i-1]] - 1
        e_city = s_city + durations[city] - 1
        itinerary.append({"day_range": f"Day {s_city}-{e_city}", "place": city})
        s_running = s_city

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    solve_itinerary()
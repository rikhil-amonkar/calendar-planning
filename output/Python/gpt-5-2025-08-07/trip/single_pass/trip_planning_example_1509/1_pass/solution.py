import json
from typing import List, Dict, Tuple, Optional, Set

def build_adjacency() -> Dict[str, Set[str]]:
    # Directed adjacency based on the provided direct flights list
    edges = []
    def add_bidirectional(a,b):
        edges.append((a,b))
        edges.append((b,a))
    def add_directed(a,b):
        edges.append((a,b))

    add_bidirectional("Warsaw", "Riga")
    add_bidirectional("Warsaw", "Tallinn")
    add_bidirectional("Copenhagen", "Helsinki")
    add_bidirectional("Lyon", "Paris")
    add_bidirectional("Copenhagen", "Warsaw")
    add_bidirectional("Lyon", "Oslo")
    add_bidirectional("Paris", "Oslo")
    add_bidirectional("Paris", "Riga")
    add_bidirectional("Krakow", "Helsinki")
    add_bidirectional("Paris", "Tallinn")
    add_bidirectional("Oslo", "Riga")
    add_bidirectional("Krakow", "Warsaw")
    add_bidirectional("Paris", "Helsinki")
    add_bidirectional("Copenhagen", "Santorini")
    add_bidirectional("Helsinki", "Warsaw")
    add_bidirectional("Helsinki", "Riga")
    add_bidirectional("Copenhagen", "Krakow")
    add_bidirectional("Copenhagen", "Riga")
    add_bidirectional("Paris", "Krakow")
    add_bidirectional("Copenhagen", "Oslo")
    add_bidirectional("Oslo", "Tallinn")
    add_bidirectional("Oslo", "Helsinki")
    add_bidirectional("Copenhagen", "Tallinn")
    add_bidirectional("Oslo", "Krakow")
    add_directed("Riga", "Tallinn")
    add_bidirectional("Helsinki", "Tallinn")
    add_bidirectional("Paris", "Copenhagen")
    add_bidirectional("Paris", "Warsaw")
    add_directed("Santorini", "Oslo")
    add_bidirectional("Oslo", "Warsaw")

    adj = {}
    for a,b in edges:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set())  # ensure key exists
    return adj

def compute_intervals_for_path(path: List[str], durations: Dict[str,int]) -> List[Tuple[int,int]]:
    intervals = []
    E_prev = 0
    for i, city in enumerate(path):
        if i == 0:
            start = 1
        else:
            start = E_prev
        end = start + durations[city] - 1
        intervals.append((start, end))
        E_prev = end
    return intervals

def satisfies_city_constraints(city: str, start: int, end: int,
                               must_cover_days: Dict[str, List[int]],
                               overlap_windows: Dict[str, Tuple[int,int]]) -> bool:
    if city in must_cover_days:
        for d in must_cover_days[city]:
            if not (start <= d <= end):
                return False
    if city in overlap_windows:
        a,b = overlap_windows[city]
        if end < a or start > b:
            return False
    return True

def future_feasibility_prune(E_prev: int, used: Set[str],
                             exact_day_cities: Dict[str, List[int]],
                             window_cities: Dict[str, Tuple[int,int]]) -> bool:
    # If key cities not yet placed, ensure we haven't passed their latest feasible start window
    # Exact-day cities (must cover both specified days) of length 2 imply their start must be the first day.
    if "Santorini" not in used and E_prev > 12:
        return False
    if "Krakow" not in used and E_prev > 17:
        return False
    if "Riga" not in used and E_prev > 23:
        return False
    # Overlap-window cities: must overlap at least one day in [a,b]; if start >= b+1 it's impossible
    if "Paris" not in used and E_prev > 8:
        return False
    if "Helsinki" not in used and E_prev > 22:
        return False
    return True

def solve_itinerary():
    total_days = 25
    cities = [
        "Paris","Warsaw","Krakow","Tallinn","Riga",
        "Copenhagen","Helsinki","Oslo","Santorini","Lyon"
    ]
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
        "Lyon": 4
    }
    must_cover_days = {
        "Krakow": [17,18],
        "Riga": [23,24],
        "Santorini": [12,13],
    }
    overlap_windows = {
        "Paris": (4,8),
        "Helsinki": (18,22),
    }

    adj = build_adjacency()

    # Verify all cities exist in adjacency (ensures no typos)
    for c in cities:
        adj.setdefault(c, set())

    # Helper to compute out-degree for heuristic ordering
    out_degree = {c: len(adj.get(c, [])) for c in cities}

    # Order for initial candidates: small out-degree first, then must-cover, then window
    def city_priority(c: str) -> Tuple[int,int,int]:
        return (out_degree[c], -len(must_cover_days.get(c, [])), -int(c in overlap_windows))

    initial_candidates = sorted(cities, key=city_priority)

    best_path = None

    def backtrack(path: List[str], used: Set[str], E_prev: int) -> Optional[List[str]]:
        nonlocal best_path
        if len(path) == len(cities):
            # Validate final E equals total_days
            if E_prev == total_days:
                best_path = path[:]
                return best_path
            return None

        # Future feasibility prune
        if not future_feasibility_prune(E_prev, used, must_cover_days, overlap_windows):
            return None

        # Determine candidate next cities
        if not path:
            candidates = initial_candidates
        else:
            last = path[-1]
            neighbors = [c for c in adj[last] if c not in used]
            # Special forced adjacency due to Santorini constraints:
            # - Santorini can only be preceded by Copenhagen (inbound unique)
            # - If last is Copenhagen and Santorini not used, force Santorini next to ensure reachability
            if last == "Copenhagen" and "Santorini" not in used:
                neighbors = ["Santorini"] if "Santorini" in neighbors else []
            # - If placing Santorini, it must have come from Copenhagen; validated when selecting it.
            # - After Santorini, only viable next is Oslo (to avoid revisiting Copenhagen), if available.
            if last == "Santorini":
                # Next must be Oslo if available and unvisited
                neighbors = [c for c in neighbors if c == "Oslo"]

            candidates = neighbors

        # Heuristic: sort candidates by how well they will satisfy constraints when placed next
        def candidate_score(c: str) -> Tuple[int,int,int,int]:
            start = 1 if not path else E_prev
            end = start + durations[c] - 1
            # Hard infeasibility checked early
            feasible = satisfies_city_constraints(c, start, end, must_cover_days, overlap_windows)
            inf = 0 if feasible else 1
            # Prefer cities with constraints that align well: compute how many required days are covered
            cover_count = 0
            for d in must_cover_days.get(c, []):
                if start <= d <= end:
                    cover_count += 1
            # Prefer lower out-degree (more constrained)
            deg = out_degree[c]
            # Prefer cities with constraints first
            return (inf, -cover_count, deg, 0)

        candidates = sorted(candidates, key=candidate_score)

        for c in candidates:
            # Additional inbound check for Santorini
            if c == "Santorini" and path and path[-1] != "Copenhagen":
                continue

            start = 1 if not path else E_prev
            end = start + durations[c] - 1

            # Check constraints for this city
            if not satisfies_city_constraints(c, start, end, must_cover_days, overlap_windows):
                continue

            # Additional prune: if placing this city makes it impossible to place remaining exact-day cities because E will overshoot
            new_E = end
            if not future_feasibility_prune(new_E, used | {c}, must_cover_days, overlap_windows):
                continue

            path.append(c)
            used.add(c)
            res = backtrack(path, used, new_E)
            if res is not None:
                return res
            used.remove(c)
            path.pop()

        return None

    solution = backtrack([], set(), 0)
    if solution is None:
        raise RuntimeError("No feasible itinerary found with the given constraints.")

    intervals = compute_intervals_for_path(solution, durations)
    itinerary = []
    for city, (s,e) in zip(solution, intervals):
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False))
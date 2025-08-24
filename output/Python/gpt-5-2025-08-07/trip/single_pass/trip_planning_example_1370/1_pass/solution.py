import json
from typing import Dict, List, Tuple, Set, Optional

def build_adjacency() -> Dict[str, Set[str]]:
    # Directed graph: add both directions for "A and B", and one-way for "from A to B"
    adj = {c: set() for c in [
        "Paris", "Krakow", "Amsterdam", "Split", "Vilnius", "Munich",
        "Geneva", "Budapest", "Santorini"
    ]}
    # Bi-directional edges
    bidir_pairs = [
        ("Paris", "Krakow"),
        ("Paris", "Amsterdam"),
        ("Paris", "Split"),
        ("Paris", "Geneva"),
        ("Amsterdam", "Geneva"),
        ("Munich", "Split"),
        ("Split", "Krakow"),
        ("Munich", "Amsterdam"),
        ("Budapest", "Amsterdam"),
        ("Split", "Geneva"),
        ("Vilnius", "Split"),
        ("Munich", "Geneva"),
        ("Munich", "Krakow"),
        ("Vilnius", "Amsterdam"),
        ("Budapest", "Paris"),
        ("Krakow", "Amsterdam"),
        ("Vilnius", "Paris"),
        ("Budapest", "Geneva"),
        ("Split", "Amsterdam"),
        ("Santorini", "Geneva"),
        ("Amsterdam", "Santorini"),
        ("Munich", "Budapest"),
        ("Munich", "Paris"),
    ]
    for a, b in bidir_pairs:
        adj[a].add(b)
        adj[b].add(a)
    # Directed edges
    adj["Vilnius"].add("Munich")        # from Vilnius to Munich
    adj["Krakow"].add("Vilnius")        # from Krakow to Vilnius
    return adj

def compute_itinerary() -> Optional[List[Tuple[str, int, int]]]:
    # City durations (days)
    durations = {
        "Santorini": 5,
        "Krakow": 5,
        "Paris": 5,
        "Vilnius": 3,
        "Munich": 5,
        "Geneva": 2,
        "Amsterdam": 4,
        "Budapest": 5,
        "Split": 4,
    }
    # Windows: city must cover inclusive day range
    windows = {
        "Santorini": (25, 29),
        "Krakow": (18, 22),
        "Paris": (11, 15),
    }

    cities = list(durations.keys())
    n = len(cities)
    adj = build_adjacency()

    # DFS search for a valid sequence (Hamiltonian path with timing constraints)
    best_path = None
    start_days: Dict[str, int] = {}

    # Pre-calc total days check (sanity)
    total_calendar_days = sum(durations.values()) - (n - 1)
    if total_calendar_days != 30:
        return None  # constraints inconsistent

    # Helper to check if city with window can start at this day
    def window_ok(city: str, start_day: int) -> bool:
        if city not in windows:
            return True
        wstart, wend = windows[city]
        L = durations[city]
        # City interval [start_day, start_day + L - 1] must fully cover [wstart, wend]
        return start_day <= wstart and (start_day + L - 1) >= wend

    # Additional prune: if we passed a window start without placing that city yet, impossible
    def window_future_possible(current_day: int, used: Set[str]) -> bool:
        for c, (wstart, _) in windows.items():
            if c not in used and current_day > wstart:
                return False
        return True

    def dfs(path: List[str], used: Set[str], next_start_day: int) -> Optional[List[str]]:
        nonlocal best_path
        if len(path) == n:
            best_path = path[:]
            return best_path

        if not window_future_possible(next_start_day, used):
            return None

        last = path[-1] if path else None

        # Candidate next cities
        candidates = []
        if last is None:
            candidates = [c for c in cities if c not in used]
        else:
            candidates = [c for c in adj[last] if c not in used]

        # Deterministic ordering to ensure stable output: prioritize window cities when they must start now
        def sort_key(c):
            # Prefer cities that must start now (window start equals next_start_day)
            must_start_now = 0
            if c in windows:
                wstart, wend = windows[c]
                if not window_ok(c, next_start_day):
                    return (1, 1, c)  # push invalid to end
                if next_start_day == wstart:
                    must_start_now = -1  # highest priority
            return (0, must_start_now, c)

        candidates.sort(key=sort_key)

        for c in candidates:
            s = next_start_day
            if not window_ok(c, s):
                continue
            # Assign and recurse
            path.append(c)
            used.add(c)
            start_days[c] = s
            next_day = s + durations[c] - 1  # next city's start (overlap on flight day)
            res = dfs(path, used, next_day)
            if res is not None:
                return res
            # backtrack
            path.pop()
            used.remove(c)
            start_days.pop(c, None)

        return None

    res = dfs([], set(), 1)
    if res is None:
        return None

    # Build itinerary ranges
    itinerary = []
    for i, city in enumerate(res):
        s = start_days[city]
        e = s + durations[city] - 1
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})
    return itinerary

def main():
    itinerary = compute_itinerary()
    if itinerary is None:
        output = {"error": "No feasible itinerary found with given constraints."}
    else:
        output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()
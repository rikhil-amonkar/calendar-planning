import json
from typing import Dict, List, Optional, Tuple, Set

def build_adjacency(direct_pairs: List[Tuple[str, str]]) -> Dict[str, Set[str]]:
    adj: Dict[str, Set[str]] = {}
    for a, b in direct_pairs:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def covers_window(start: int, end: int, window: Optional[Tuple[int, int]]) -> bool:
    if not window:
        return True
    a, b = window
    return start <= a and end >= b

def validate_solution(segments: List[Tuple[str, int, int]],
                      durations: Dict[str, int],
                      windows: Dict[str, Optional[Tuple[int, int]]],
                      adj: Dict[str, Set[str]],
                      total_days: int) -> bool:
    # Check total coverage from Day 1 to total_days without gaps
    if not segments:
        return False
    if segments[0][1] != 1:
        return False
    if segments[-1][2] != total_days:
        return False
    # Check consecutive overlaps and flights
    for i in range(len(segments) - 1):
        curr_city, s1, e1 = segments[i]
        next_city, s2, e2 = segments[i + 1]
        # Overlap on boundary day
        if s2 != e1:
            return False
        # Direct flight
        if next_city not in adj.get(curr_city, set()):
            return False
    # Check each city once, durations and window coverage
    seen = set()
    for city, s, e in segments:
        if city in seen:
            return False
        seen.add(city)
        if (e - s + 1) != durations[city]:
            return False
        if not covers_window(s, e, windows.get(city)):
            return False
    return True

def solve_itinerary(cities: List[str],
                    durations: Dict[str, int],
                    windows: Dict[str, Optional[Tuple[int, int]]],
                    direct_pairs: List[Tuple[str, str]],
                    total_days: int) -> List[Tuple[str, int, int]]:
    adj = build_adjacency(direct_pairs)

    # DFS backtracking search
    def dfs(order: List[str],
            segments: List[Tuple[str, int, int]],
            prev_city: Optional[str],
            next_start_day: int,
            remaining: Set[str]) -> Optional[List[Tuple[str, int, int]]]:
        if not remaining:
            # All placed, validate end day equals total_days
            if segments and segments[-1][2] == total_days:
                return segments
            return None

        candidates = []
        for c in remaining:
            # Direct flight requirement (except for first city)
            if prev_city is not None and c not in adj.get(prev_city, set()):
                continue
            s = next_start_day
            d = durations[c]
            e = s + d - 1
            # Window feasibility
            if not covers_window(s, e, windows.get(c)):
                continue
            # Heuristic priority
            prio = 2
            w = windows.get(c)
            if w:
                a, b = w
                if a == s and (b - a + 1) == d:
                    prio = 0
                else:
                    prio = 1
            candidates.append((prio, c, s, e))

        # Sort by priority, then by name for determinism
        candidates.sort(key=lambda x: (x[0], x[1]))

        for _, c, s, e in candidates:
            new_order = order + [c]
            new_segments = segments + [(c, s, e)]
            sol = dfs(new_order, new_segments, c, e, remaining - {c})
            if sol is not None:
                return sol
        return None

    # Start on Day 1
    solution = dfs([], [], None, 1, set(cities))
    if solution is None or not validate_solution(solution, durations, windows, build_adjacency(direct_pairs), total_days):
        raise RuntimeError("No feasible itinerary found under given constraints.")
    return solution

def main():
    # Input variables (constraints)
    total_days = 27
    cities = [
        "Warsaw", "Porto", "Naples", "Brussels", "Split",
        "Reykjavik", "Amsterdam", "Lyon", "Helsinki", "Valencia"
    ]
    durations = {
        "Warsaw": 3,
        "Porto": 5,
        "Naples": 4,
        "Brussels": 3,
        "Split": 3,
        "Reykjavik": 5,
        "Amsterdam": 4,
        "Lyon": 3,
        "Helsinki": 4,
        "Valencia": 2
    }
    # Required presence windows (inclusive)
    windows = {
        "Porto": (1, 5),        # Workshop between Day 1 and Day 5
        "Amsterdam": (5, 8),    # Visit relatives between Day 5 and Day 8
        "Helsinki": (8, 11),    # Wedding between Day 8 and Day 11
        "Naples": (17, 20),     # Conference during Day 17 and Day 20
        "Brussels": (20, 22),   # Annual show from Day 20 to Day 22
        "Warsaw": None,
        "Split": None,
        "Reykjavik": None,
        "Lyon": None,
        "Valencia": None
    }
    # Direct flights (undirected pairs)
    direct_pairs = [
        ("Amsterdam", "Warsaw"),
        ("Helsinki", "Brussels"),
        ("Helsinki", "Warsaw"),
        ("Reykjavik", "Brussels"),
        ("Amsterdam", "Lyon"),
        ("Amsterdam", "Naples"),
        ("Amsterdam", "Reykjavik"),
        ("Naples", "Valencia"),
        ("Porto", "Brussels"),
        ("Amsterdam", "Split"),
        ("Lyon", "Split"),
        ("Warsaw", "Split"),
        ("Porto", "Amsterdam"),
        ("Helsinki", "Split"),
        ("Brussels", "Lyon"),
        ("Porto", "Lyon"),
        ("Reykjavik", "Warsaw"),
        ("Brussels", "Valencia"),
        ("Valencia", "Lyon"),
        ("Porto", "Warsaw"),
        ("Warsaw", "Valencia"),
        ("Amsterdam", "Helsinki"),
        ("Porto", "Valencia"),
        ("Warsaw", "Brussels"),
        ("Warsaw", "Naples"),
        ("Naples", "Split"),
        ("Helsinki", "Naples"),
        ("Helsinki", "Reykjavik"),
        ("Amsterdam", "Valencia"),
        ("Naples", "Brussels")
    ]

    segments = solve_itinerary(cities, durations, windows, direct_pairs, total_days)

    # Format output
    itinerary = []
    for city, s, e in segments:
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
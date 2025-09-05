import json
from typing import List, Dict, Tuple, Optional, Set

def build_graph(direct_pairs: List[Tuple[str, str]]) -> Dict[str, Set[str]]:
    graph: Dict[str, Set[str]] = {}
    for a, b in direct_pairs:
        graph.setdefault(a, set()).add(b)
        graph.setdefault(b, set()).add(a)
    return graph

def compute_itinerary(
    cities: List[str],
    durations: Dict[str, int],
    mandatory_windows: Dict[str, Tuple[int, int]],
    direct_pairs: List[Tuple[str, str]],
    total_days: int
) -> Optional[List[Tuple[str, int, int]]]:
    n = len(cities)
    # Validate total day feasibility: sum(durations) - (n-1) must equal total_days
    if sum(durations[c] for c in cities) - (n - 1) != total_days:
        return None

    graph = build_graph(direct_pairs)

    # DFS with pruning
    def dfs(path: List[str], used: Set[str], prev: Optional[str], pos: int, start_day: int) -> Optional[List[str]]:
        # Prune: if we have unvisited fixed cities whose required start day has already passed
        for city, (req_start, _) in mandatory_windows.items():
            if city not in used and req_start < start_day:
                return None

        # Determine if current position must be a mandatory start city
        forced_candidates = [city for city, (req_start, _) in mandatory_windows.items()
                             if city not in used and req_start == start_day]

        # Build candidate list
        if forced_candidates:
            candidates = forced_candidates
        else:
            candidates = [c for c in cities if c not in used]

        # Order candidates to help search (heuristics: adjacency count descending, durations descending)
        def cand_key(c):
            deg = len(graph.get(c, []))
            return (-deg, -durations[c], c)
        candidates.sort(key=cand_key)

        for city in candidates:
            if prev is not None:
                # must be directly connected to previous city
                if city not in graph.get(prev, set()):
                    continue

            # Check fixed window match if any
            end_day = start_day + durations[city] - 1
            if city in mandatory_windows:
                req_start, req_end = mandatory_windows[city]
                if start_day != req_start or end_day != req_end:
                    continue

            # Place city
            path.append(city)
            used.add(city)

            if len(path) == n:
                # Final city must cover until total_days
                if end_day == total_days:
                    return path
                # else backtrack
            else:
                # Next start_day equals today's end_day (1-day overlap on flight day)
                res = dfs(path, used, city, pos + 1, end_day)
                if res is not None:
                    return res

            # backtrack
            used.remove(city)
            path.pop()

        return None

    # Start search
    path = dfs([], set(), None, 0, 1)
    if path is None:
        return None

    # Build day ranges from path
    itinerary_ranges: List[Tuple[str, int, int]] = []
    current_start = 1
    for city in path:
        end_day = current_start + durations[city] - 1
        itinerary_ranges.append((city, current_start, end_day))
        current_start = end_day  # next starts on the overlap day

    return itinerary_ranges

def main():
    # Define inputs
    cities = [
        "Venice", "Reykjavik", "Munich", "Santorini", "Manchester",
        "Porto", "Bucharest", "Tallinn", "Valencia", "Vienna"
    ]
    durations = {
        "Venice": 3,
        "Reykjavik": 2,
        "Munich": 3,
        "Santorini": 3,
        "Manchester": 3,
        "Porto": 3,
        "Bucharest": 5,
        "Tallinn": 4,
        "Valencia": 2,
        "Vienna": 5
    }
    # Mandatory windows: exact day ranges
    mandatory_windows = {
        "Munich": (4, 6),
        "Santorini": (8, 10),
        "Valencia": (14, 15),
    }
    total_days = 24

    # Parse direct flights (undirected)
    direct_pairs = [
        ("Bucharest", "Manchester"),
        ("Munich", "Venice"),
        ("Santorini", "Manchester"),
        ("Vienna", "Reykjavik"),
        ("Venice", "Santorini"),
        ("Munich", "Porto"),
        ("Valencia", "Vienna"),
        ("Manchester", "Vienna"),
        ("Porto", "Vienna"),
        ("Venice", "Manchester"),
        ("Santorini", "Vienna"),
        ("Munich", "Manchester"),
        ("Munich", "Reykjavik"),
        ("Bucharest", "Valencia"),
        ("Venice", "Vienna"),
        ("Bucharest", "Vienna"),
        ("Porto", "Manchester"),
        ("Munich", "Vienna"),
        ("Valencia", "Porto"),
        ("Munich", "Bucharest"),
        ("Tallinn", "Munich"),
        ("Santorini", "Bucharest"),
        ("Munich", "Valencia"),
    ]

    itinerary_ranges = compute_itinerary(cities, durations, mandatory_windows, direct_pairs, total_days)
    if itinerary_ranges is None:
        print(json.dumps({"error": "No feasible itinerary found with given constraints."}))
        return

    # Format output
    output_itinerary = []
    for city, start, end in itinerary_ranges:
        output_itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": output_itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
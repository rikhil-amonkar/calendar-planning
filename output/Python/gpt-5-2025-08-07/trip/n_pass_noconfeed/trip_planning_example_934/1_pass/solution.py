import json
from typing import List, Dict, Tuple, Optional, Set

def build_adjacency() -> Dict[str, Set[str]]:
    adj = {c: set() for c in [
        "Brussels", "Rome", "Dubrovnik", "Geneva", "Budapest", "Riga", "Valencia"
    ]}
    def add_edge(a: str, b: str, bidir: bool = True):
        adj[a].add(b)
        if bidir:
            adj[b].add(a)

    # Bidirectional direct flights
    add_edge("Brussels", "Valencia", True)
    add_edge("Rome", "Valencia", True)
    add_edge("Brussels", "Geneva", True)
    add_edge("Rome", "Geneva", True)
    add_edge("Dubrovnik", "Geneva", True)
    add_edge("Valencia", "Geneva", True)
    add_edge("Geneva", "Budapest", True)
    add_edge("Riga", "Brussels", True)
    add_edge("Rome", "Budapest", True)
    add_edge("Rome", "Brussels", True)
    add_edge("Brussels", "Budapest", True)
    add_edge("Dubrovnik", "Rome", True)

    # One-way direct flight
    adj["Rome"].add("Riga")  # from Rome to Riga

    return adj

def find_itinerary(
    total_days: int,
    durations: Dict[str, int],
    brussels_window: Tuple[int, int],
    riga_meet_window: Tuple[int, int],
    budapest_window: Tuple[int, int],
    cities: List[str],
    adjacency: Dict[str, Set[str]]
) -> Optional[Tuple[List[str], Dict[str, int], Dict[str, int]]]:
    # Depth-first search over permutations with pruning using constraints
    remaining = set(cities)
    s_map: Dict[str, int] = {}
    e_map: Dict[str, int] = {}

    def dfs(path: List[str], s_current: int, remaining: Set[str]) -> Optional[List[str]]:
        if len(path) == len(cities):
            # Ensure the final day ends exactly at total_days
            last_city = path[-1]
            if e_map[last_city] == total_days:
                return path
            return None

        # Try candidates in deterministic order for reproducibility
        for candidate in sorted(remaining):
            # Budapest must be the last city and must cover exactly the budapest_window
            if candidate == "Budapest" and len(remaining) != 1:
                continue

            # Adjacency check
            if path:
                prev = path[-1]
                if candidate not in adjacency.get(prev, set()):
                    continue

            L = durations[candidate]
            s_cand = s_current
            e_cand = s_cand + L - 1

            # Do not exceed the total calendar (shouldn't happen before last given sums, but keep robust)
            if e_cand > total_days:
                continue

            # Brussels must start exactly on brussels_window[0] (given it must be 5 days covering 7-11)
            if candidate == "Brussels":
                if s_cand != brussels_window[0]:
                    continue
                # Implicitly ensures e_cand == brussels_window[1], since L must match duration
                if e_cand != brussels_window[1]:
                    continue
            else:
                # If Brussels not yet placed, we cannot pass day 7 before placing it
                if "Brussels" not in path and "Brussels" in remaining:
                    # After placing candidate, the next start day will be e_cand
                    # We must ensure we don't skip beyond day 7
                    if e_cand > brussels_window[0]:
                        continue

            # Riga must overlap the meet window [4,7]
            if candidate == "Riga":
                if not (e_cand >= riga_meet_window[0] and s_cand <= riga_meet_window[1]):
                    continue

            # Budapest must be last and exactly cover its window (16-17)
            if candidate == "Budapest":
                if s_cand != budapest_window[0] or e_cand != budapest_window[1]:
                    continue

            # Record placement
            path.append(candidate)
            s_map[candidate] = s_cand
            e_map[candidate] = e_cand
            new_remaining = set(remaining)
            new_remaining.remove(candidate)

            # Next city's start equals this city's end due to travel-day overlap rule
            res = dfs(path, e_cand, new_remaining)
            if res:
                return res

            # Backtrack
            path.pop()
            del s_map[candidate]
            del e_map[candidate]

        return None

    result_path = dfs([], 1, remaining)
    if result_path:
        return result_path, s_map, e_map
    return None

def main():
    # Input variables (constraints)
    total_days = 17
    cities = ["Brussels", "Rome", "Dubrovnik", "Geneva", "Budapest", "Riga", "Valencia"]
    durations = {
        "Brussels": 5,
        "Rome": 2,
        "Dubrovnik": 3,
        "Geneva": 5,
        "Budapest": 2,
        "Riga": 4,
        "Valencia": 2
    }
    # Specific windows (inclusive)
    brussels_window = (7, 11)      # Must attend workshop in Brussels between day 7 and 11 (5 days exactly)
    riga_meet_window = (4, 7)      # Must meet friends in Riga between day 4 and 7
    budapest_window = (16, 17)     # Must meet friend in Budapest between day 16 and 17 (stay 2 days)

    adjacency = build_adjacency()

    res = find_itinerary(
        total_days=total_days,
        durations=durations,
        brussels_window=brussels_window,
        riga_meet_window=riga_meet_window,
        budapest_window=budapest_window,
        cities=cities,
        adjacency=adjacency
    )

    if not res:
        print(json.dumps({"error": "No valid itinerary found given the constraints."}))
        return

    path, s_map, e_map = res

    # Build itinerary output
    itinerary = []
    for city in path:
        itinerary.append({
            "day_range": f"Day {s_map[city]}-{e_map[city]}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
import json
from typing import Dict, List, Tuple, Optional

def build_adjacency() -> Dict[str, set]:
    cities = ["Hamburg","Stockholm","Vienna","Paris","Edinburgh","Riga","Barcelona","Krakow"]
    adj = {c: set() for c in cities}
    undirected_pairs = [
        ("Hamburg","Stockholm"),
        ("Vienna","Stockholm"),
        ("Paris","Edinburgh"),
        ("Riga","Barcelona"),
        ("Paris","Riga"),
        ("Krakow","Barcelona"),
        ("Edinburgh","Stockholm"),
        ("Paris","Krakow"),
        ("Krakow","Stockholm"),
        ("Riga","Edinburgh"),
        ("Barcelona","Stockholm"),
        ("Paris","Stockholm"),
        ("Krakow","Edinburgh"),
        ("Vienna","Hamburg"),
        ("Paris","Hamburg"),
        ("Riga","Stockholm"),
        ("Hamburg","Barcelona"),
        ("Vienna","Barcelona"),
        ("Krakow","Vienna"),
        ("Barcelona","Edinburgh"),
        ("Paris","Barcelona"),
        ("Hamburg","Edinburgh"),
        ("Paris","Vienna"),
        ("Vienna","Riga"),
    ]
    for a,b in undirected_pairs:
        adj[a].add(b)
        adj[b].add(a)
    # Directed edge: from Riga to Hamburg
    adj["Riga"].add("Hamburg")
    return adj

def compute_itinerary() -> Optional[List[Tuple[str, int, int]]]:
    total_days = 16

    # City durations
    durations: Dict[str, int] = {
        "Vienna": 4,
        "Barcelona": 2,
        "Edinburgh": 4,
        "Krakow": 3,
        "Riga": 4,
        "Hamburg": 2,
        "Paris": 2,
        "Stockholm": 2,
    }

    # Must-be windows (inclusive): city -> (start_day, end_day)
    windows: Dict[str, Tuple[int, int]] = {
        "Paris": (1, 2),            # Wedding
        "Hamburg": (10, 11),        # Conference
        "Edinburgh": (12, 15),      # Meet friend
        "Stockholm": (15, 16),      # Visit relatives
    }

    # Pre-calc
    city_list = list(durations.keys())
    adjacency = build_adjacency()
    S = sum(durations.values())
    N = len(durations)
    assert S - (N - 1) == total_days, "Durations and overlaps inconsistent with total days"

    # Heuristic ordering for candidate selection
    def candidate_order(cands: List[str]) -> List[str]:
        # Prefer cities with windows (tight constraints) first to reduce search
        return sorted(cands, key=lambda c: (0 if c in windows else 1, c))

    # Pruning: can windows still be met given current end day?
    def window_feasible(current_end: int, remaining: List[str]) -> bool:
        # current_end is the s for the next city to be placed
        # For any city with a fixed start S*, its possible start s belongs to
        # [current_end, current_end + sum(d_i - 1 for i in remaining if i != city)]
        # If S* not in this range, infeasible.
        base = current_end
        rem_deltas = {c: durations[c] - 1 for c in remaining}
        total_delta_all = sum(rem_deltas.values())
        for c in remaining:
            if c in windows:
                must_start, _ = windows[c]
                max_extra = total_delta_all - rem_deltas[c]
                if not (base <= must_start <= base + max_extra):
                    return False
        return True

    best_route: Optional[List[Tuple[str,int,int]]] = None

    def backtrack(route: List[Tuple[str,int,int]], unused: set):
        nonlocal best_route
        if best_route is not None:
            return  # stop at first feasible itinerary

        k = len(route)
        if k == 0:
            s = 1
            # If any city has must_start == s, restrict to those
            must_start_cands = [c for c in unused if (c in windows and windows[c][0] == s)]
            cands = must_start_cands if must_start_cands else list(unused)
            for c in candidate_order(cands):
                d = durations[c]
                e = s + d - 1
                if e > total_days:
                    continue
                if c in windows:
                    ms, me = windows[c]
                    if s != ms or e != me:
                        continue
                # Prune feasibility for future windows
                rem = list(unused - {c})
                if not window_feasible(e, rem):
                    continue
                route.append((c, s, e))
                backtrack(route, unused - {c})
                route.pop()
        else:
            prev_city, _, prev_e = route[-1]
            s = prev_e
            # If any unused city must start at s, restrict to those first
            must_start_cands = [c for c in unused if (c in windows and windows[c][0] == s)]
            cands = must_start_cands if must_start_cands else list(unused)
            for c in candidate_order(cands):
                if c not in adjacency.get(prev_city, set()):
                    continue
                d = durations[c]
                e = s + d - 1
                if e > total_days:
                    continue
                if c in windows:
                    ms, me = windows[c]
                    if s != ms or e != me:
                        continue
                rem = list(unused - {c})
                # If this is the last city, ensure it ends at total_days
                remaining_after = len(rem)
                # Compute final end if we pick c now and then add remaining others:
                # e_final = sum(d for assigned incl c) - (num_assigned_incl_c - 1)
                # But equivalently, with fixed S and N, it's guaranteed to be total_days if all cities used.
                # However, to be safe, ensure that placing c here doesn't make it impossible to finish:
                # Check feasibility of windows for remaining cities:
                if not window_feasible(e, rem):
                    continue
                route.append((c, s, e))
                if remaining_after == 0:
                    # Verify final end day equals total_days
                    if e == total_days:
                        best_route = route.copy()
                        return
                else:
                    backtrack(route, unused - {c})
                route.pop()

    backtrack([], set(city_list))
    return best_route

def main():
    route = compute_itinerary()
    if not route:
        output = {"itinerary": []}
    else:
        itinerary = []
        for city, s, e in route:
            itinerary.append({"day_range": f"Day {s}-{e}", "place": city})
        output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()
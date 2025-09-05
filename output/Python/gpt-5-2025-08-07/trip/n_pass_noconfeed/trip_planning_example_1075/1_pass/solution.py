import json
from typing import List, Dict, Tuple, Optional

def build_itinerary():
    # Input variables based on the user's constraints
    total_days = 25
    city_durations = {
        "Vienna": 4,
        "Lyon": 3,
        "Edinburgh": 4,
        "Reykjavik": 5,
        "Stuttgart": 5,
        "Manchester": 2,
        "Split": 5,
        "Prague": 4,
    }
    # Anchored constraints: specific day windows required
    anchors = {
        "Edinburgh": {"start": 5, "end": 8},  # must be in Edinburgh days 5-8
        "Split": {"start": 19, "end": 23},    # must be in Split days 19-23
    }

    # Direct flights (treated as undirected)
    direct_pairs = [
        ("Reykjavik", "Stuttgart"),
        ("Stuttgart", "Split"),
        ("Stuttgart", "Vienna"),
        ("Prague", "Manchester"),
        ("Edinburgh", "Prague"),
        ("Manchester", "Split"),
        ("Prague", "Vienna"),
        ("Vienna", "Manchester"),
        ("Prague", "Split"),
        ("Vienna", "Lyon"),
        ("Stuttgart", "Edinburgh"),
        ("Split", "Lyon"),
        ("Stuttgart", "Manchester"),
        ("Prague", "Lyon"),
        ("Reykjavik", "Vienna"),
        ("Prague", "Reykjavik"),
        ("Vienna", "Split"),
    ]
    flights = {frozenset([a, b]) for a, b in direct_pairs}

    cities = list(city_durations.keys())
    n = len(cities)

    # Quick feasibility checks
    if sum(city_durations.values()) - (n - 1) != total_days:
        # Overlap rule requires this identity to hold
        raise ValueError("Infeasible durations given total days and number of cities.")

    d_minus_1 = {c: city_durations[c] - 1 for c in cities}

    def has_direct(a: str, b: str) -> bool:
        return frozenset([a, b]) in flights

    # Backtracking to find a valid order satisfying direct flights and anchors
    best_order: Optional[List[str]] = None

    # For deterministic behavior
    cities_sorted = sorted(cities)

    def backtrack(path: List[str], sum_d1: int) -> Optional[List[str]]:
        nonlocal best_order
        if len(path) == 0:
            candidates = cities_sorted
        else:
            last = path[-1]
            candidates = [c for c in cities_sorted if c not in path and has_direct(last, c)]

        for c in candidates:
            # Start day for city c is 1 + sum of (d-1) for prior cities
            start_c = 1 + sum_d1

            # Check anchored start if applicable
            if c in anchors:
                if anchors[c]["start"] != start_c:
                    continue

            # Compute new sum after adding this city
            new_sum = sum_d1 + d_minus_1[c]

            # Prune: ensure we haven't overshot any required anchor start for remaining anchored cities
            for anc_city, anc in anchors.items():
                if anc_city in path or anc_city == c:
                    continue
                # For anc_city to start at anc["start"], we need sum before it equals anc["start"] - 1
                # After adding c, sum is new_sum; if new_sum > anc["start"] - 1, we overshot and can't go back
                if new_sum > (anc["start"] - 1):
                    break
            else:
                # If not broken out (no overshoot), proceed
                new_path = path + [c]

                if len(new_path) == n:
                    # Verify final end day equals total_days
                    # End day after placing all cities is sum(durations) - (n-1)
                    final_end = sum(city_durations.values()) - (n - 1)
                    if final_end != total_days:
                        continue

                    # Validate anchored end days
                    # Compute exact start/end ranges for this full path
                    starts = {}
                    ends = {}
                    s = 1
                    for i, city in enumerate(new_path):
                        starts[city] = s
                        ends[city] = s + city_durations[city] - 1
                        if i < n - 1:
                            s = s + city_durations[city] - 1

                    valid = True
                    for anc_city, anc in anchors.items():
                        if starts[anc_city] != anc["start"] or ends[anc_city] != anc["end"]:
                            valid = False
                            break
                    if not valid:
                        continue

                    # Validate all edges in path are direct
                    if all(has_direct(new_path[i], new_path[i + 1]) for i in range(n - 1)):
                        best_order = new_path
                        return best_order
                else:
                    res = backtrack(new_path, new_sum)
                    if res is not None:
                        return res

        return None

    solution_order = backtrack([], 0)
    if solution_order is None:
        # If not found (shouldn't happen with given constraints), output empty itinerary
        return {"itinerary": []}

    # Build the day ranges for the solution
    itinerary = []
    current_start = 1
    for i, city in enumerate(solution_order):
        start_day = current_start
        end_day = start_day + city_durations[city] - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })
        if i < len(solution_order) - 1:
            current_start = end_day  # Overlap on flight day

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = build_itinerary()
    print(json.dumps(result, ensure_ascii=False))
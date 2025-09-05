import itertools
import json
from typing import List, Tuple, Dict

def main():
    # Input variables (trip constraints)
    total_days = 21
    cities = ["Manchester", "Istanbul", "Venice", "Krakow", "Lyon"]
    required_days = {
        "Manchester": 3,
        "Istanbul": 7,
        "Venice": 7,
        "Krakow": 6,
        "Lyon": 2,
    }
    # Direct flights (undirected)
    direct_flights = {
        frozenset(("Manchester", "Venice")),
        frozenset(("Manchester", "Istanbul")),
        frozenset(("Venice", "Istanbul")),
        frozenset(("Istanbul", "Krakow")),
        frozenset(("Venice", "Lyon")),
        frozenset(("Lyon", "Istanbul")),
        frozenset(("Manchester", "Krakow")),
    }
    # Event windows (inclusive day indices)
    events = [
        {"city": "Manchester", "window": (1, 3)},  # wedding between day 1 and day 3
        {"city": "Venice", "window": (3, 9)},      # workshop between day 3 and day 9
    ]

    # Basic feasibility checks
    S = sum(required_days[c] for c in cities)
    min_flights = len(cities) - 1
    # Each flight day is double-counted, so total counted city-days = total_days + number_of_flights
    # We must use exactly min_flights flights to visit all cities in a single path.
    if S != total_days + min_flights:
        raise ValueError("Inconsistent constraints: sum of required days must equal total_days + (number of flights).")

    def is_direct(a: str, b: str) -> bool:
        return frozenset((a, b)) in direct_flights

    def valid_path(order: Tuple[str, ...]) -> bool:
        # Must have a direct flight between each consecutive pair
        return all(is_direct(order[i], order[i+1]) for i in range(len(order)-1))

    def compute_intervals(order: Tuple[str, ...]) -> Dict[str, Tuple[int, int]]:
        """
        For a given order of cities, compute the inclusive day intervals for each city,
        where consecutive intervals overlap by one day to represent flight days.
        interval[order[0]] = [1, B0] with B0 = c0
        interval[order[1]] = [B0, B1] with B1 = c0 + c1 - 1
        ...
        interval[order[4]] = [B3, 21] with B3 = c0 + c1 + c2 + c3 - 3 == 22 - c4
        """
        counts = [required_days[city] for city in order]
        B0 = counts[0]
        B1 = counts[0] + counts[1] - 1
        B2 = counts[0] + counts[1] + counts[2] - 2
        B3 = counts[0] + counts[1] + counts[2] + counts[3] - 3
        # Sanity check for final boundary consistency with last city's required days
        if B3 != 22 - counts[4]:
            # Inconsistent (shouldn't happen if sums are correct), but check anyway
            return {}
        intervals = {
            order[0]: (1, B0),
            order[1]: (B0, B1),
            order[2]: (B1, B2),
            order[3]: (B2, B3),
            order[4]: (B3, 21),
        }
        return intervals

    def overlap_len(a: Tuple[int, int], b: Tuple[int, int]) -> int:
        s = max(a[0], b[0])
        e = min(a[1], b[1])
        return max(0, e - s + 1)

    best = None  # (score, order, intervals)
    # We will score by maximizing total overlap with required event windows
    for order in itertools.permutations(cities):
        if not valid_path(order):
            continue
        intervals = compute_intervals(order)
        if not intervals:
            continue

        # Check event constraints (must have non-zero overlap)
        ok = True
        score = 0
        for ev in events:
            c = ev["city"]
            w = ev["window"]
            iv = intervals[c]
            ov = overlap_len(iv, w)
            if ov == 0:
                ok = False
                break
            score += ov
        if not ok:
            continue

        # Keep best by highest score, then by earliest Venice coverage around [3,9] (tie-break)
        # Secondary tie-break: lexicographic order of city names tuple for determinism.
        tie_break = (
            -abs(intervals["Venice"][0] - events[1]["window"][0])
            -abs(intervals["Venice"][1] - events[1]["window"][1])
        )
        candidate = (score, tie_break, order, intervals)
        if best is None or candidate > best:
            best = candidate

    if best is None:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    _, _, best_order, best_intervals = best

    # Build itinerary list in trip order
    itinerary = []
    for city in best_order:
        s, e = best_intervals[city]
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
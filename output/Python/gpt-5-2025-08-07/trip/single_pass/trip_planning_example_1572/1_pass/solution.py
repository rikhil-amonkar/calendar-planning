import json
from typing import Dict, List, Tuple, Set, Optional

def build_adjacency(flights: List[Tuple[str, str]]) -> Dict[str, Set[str]]:
    adj = {}
    for a, b in flights:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def compute_allowed_start_ranges(
    cities: List[str],
    durations: Dict[str, int],
    total_days: int,
    must_days: Dict[str, List[int]]
) -> Dict[str, Tuple[int, int]]:
    ranges = {}
    for c in cities:
        d = durations[c]
        latest_start_global = total_days - d + 1
        if c in must_days and must_days[c]:
            days = sorted(must_days[c])
            min_m, max_m = min(days), max(days)
            earliest = max(1, max_m - d + 1)
            latest = min(min_m, latest_start_global)
            if earliest > latest:
                raise ValueError(f"Infeasible must-days for {c}")
            ranges[c] = (earliest, latest)
        else:
            ranges[c] = (1, latest_start_global)
    return ranges

def start_day_for_position(order: List[str], durations: Dict[str, int]) -> int:
    # Start day of the last city appended in order
    i = len(order)  # position index starting at 1
    sum_prev = sum(durations[c] for c in order[:-1])
    return 1 + sum_prev - (i - 1)

def next_start_day(order: List[str], durations: Dict[str, int]) -> int:
    # Start day of the next (not yet appended) city if appended next
    i = len(order)  # current last index
    sum_upto = sum(durations[c] for c in order)
    return 1 + sum_upto - i

def end_day(start: int, duration: int) -> int:
    return start + duration - 1

def solve_itinerary(
    total_days: int,
    cities: List[str],
    durations: Dict[str, int],
    flights: List[Tuple[str, str]],
    must_days: Dict[str, List[int]]
) -> Optional[List[Tuple[str, int, int]]]:
    adj = build_adjacency(flights)
    ranges = compute_allowed_start_ranges(cities, durations, total_days, must_days)

    # Backtracking search
    best_order = []

    def feasible_last_city(city: str, start: int) -> bool:
        # Ensure that the last city's end day equals total_days
        return end_day(start, durations[city]) == total_days

    def backtrack(order: List[str], used: Set[str]) -> Optional[List[str]]:
        # Prune based on inability to meet future anchored starts
        if order:
            # Check the just-placed city's start within allowed range
            c = order[-1]
            sd = start_day_for_position(order, durations)
            lo, hi = ranges[c]
            if not (lo <= sd <= hi):
                return None

            # Check adjacency with previous
            if len(order) >= 2:
                prev = order[-2]
                if c not in adj.get(prev, set()):
                    return None

        # If full order built, validate end day and all constraints
        if len(order) == len(cities):
            # End day must be total_days
            last_city = order[-1]
            sd_last = start_day_for_position(order, durations)
            if not feasible_last_city(last_city, sd_last):
                return None
            # Ensure all must-days are included by their city blocks (already enforced by ranges),
            # and that first day starts at 1 (guaranteed by formula if first is placed correctly).
            return order

        # Prune: if next possible start day exceeds latest start for any unplaced anchored city
        nsd = next_start_day(order, durations) if order else 1
        for c in cities:
            if c not in used:
                # If city has must-days constraint, ensure we haven't passed its latest start possibility
                lo, hi = ranges[c]
                if nsd > hi:
                    return None

        # Candidate next cities
        remaining = [c for c in cities if c not in used]

        # Heuristic: if first city not placed, prefer ones with earliest required start (e.g., Berlin)
        if not order:
            # Filter to those whose allowed start includes day 1
            preferred = [c for c in remaining if ranges[c][0] <= 1 <= ranges[c][1]]
            candidates = preferred if preferred else remaining
        else:
            # Prefer neighbors of prev to reduce dead-ends
            prev = order[-1]
            neighbors = [c for c in remaining if c in adj.get(prev, set())]
            candidates = neighbors if neighbors else remaining

        # Additional heuristic: try cities with tighter latest start first
        candidates.sort(key=lambda x: (ranges[x][1], ranges[x][0], -durations[x]))

        for c in candidates:
            # Compute the start day if we place c next
            tentative_order = order + [c]
            sd = start_day_for_position(tentative_order, durations)
            lo, hi = ranges[c]
            # Quick range check
            if not (lo <= sd <= hi):
                continue

            # If this is the last city, check it finishes on total_days
            if len(tentative_order) == len(cities):
                if not feasible_last_city(c, sd):
                    continue

            res = backtrack(tentative_order, used | {c})
            if res is not None:
                return res
        return None

    order = backtrack([], set())
    if order is None:
        return None

    # Build the itinerary with day ranges
    itinerary = []
    current_start = 1
    for i, city in enumerate(order):
        if i == 0:
            start = 1
        else:
            # Overlap on travel day
            start = end_day  # placeholder to avoid confusion
        # Use the formula
        sd = 1 + sum(durations[c] for c in order[:i]) - i
        ed = sd + durations[city] - 1
        itinerary.append((city, sd, ed))
    return itinerary

def main():
    # Input variables as per the problem statement
    total_days = 23
    cities = [
        "Lyon", "Paris", "Riga", "Berlin", "Stockholm",
        "Zurich", "Nice", "Seville", "Milan", "Naples"
    ]
    durations = {
        "Lyon": 3,
        "Paris": 5,
        "Riga": 2,
        "Berlin": 2,
        "Stockholm": 3,
        "Zurich": 5,
        "Nice": 2,
        "Seville": 3,
        "Milan": 3,
        "Naples": 4,
    }
    # Must be in city on specific days (inclusive)
    must_days = {
        # Wedding in Berlin between day 1 and day 2
        "Berlin": [1, 2],
        # Workshop in Nice between day 12 and day 13
        "Nice": [12, 13],
        # Show in Stockholm from day 20 to day 22
        "Stockholm": [20, 21, 22],
    }
    # Direct flights (undirected)
    flights = [
        ("Paris", "Stockholm"),
        ("Seville", "Paris"),
        ("Naples", "Zurich"),
        ("Nice", "Riga"),
        ("Berlin", "Milan"),
        ("Paris", "Zurich"),
        ("Paris", "Nice"),
        ("Milan", "Paris"),
        ("Milan", "Riga"),
        ("Paris", "Lyon"),
        ("Milan", "Naples"),
        ("Paris", "Riga"),
        ("Berlin", "Stockholm"),
        ("Stockholm", "Riga"),
        ("Nice", "Zurich"),
        ("Milan", "Zurich"),
        ("Lyon", "Nice"),
        ("Zurich", "Stockholm"),
        ("Zurich", "Riga"),
        ("Berlin", "Naples"),
        ("Milan", "Stockholm"),
        ("Berlin", "Zurich"),
        ("Milan", "Seville"),
        ("Paris", "Naples"),
        ("Berlin", "Riga"),
        ("Nice", "Stockholm"),
        ("Berlin", "Paris"),
        ("Nice", "Naples"),
        ("Berlin", "Nice"),
    ]

    itinerary = solve_itinerary(total_days, cities, durations, flights, must_days)
    if itinerary is None:
        output = {"itinerary": []}
    else:
        # Format as required
        formatted = []
        for city, sd, ed in itinerary:
            formatted.append({
                "day_range": f"Day {sd}-{ed}",
                "place": city
            })
        output = {"itinerary": formatted}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()
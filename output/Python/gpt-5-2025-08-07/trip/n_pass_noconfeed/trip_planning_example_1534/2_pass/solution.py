import json
from typing import List, Dict, Tuple, Set

def build_adjacency():
    # Undirected edges (both directions)
    undirected_pairs = [
        ("Paris", "Venice"),
        ("Barcelona", "Amsterdam"),
        ("Amsterdam", "Warsaw"),
        ("Amsterdam", "Vilnius"),
        ("Barcelona", "Warsaw"),
        ("Warsaw", "Venice"),
        ("Amsterdam", "Hamburg"),
        ("Barcelona", "Hamburg"),
        ("Barcelona", "Florence"),
        ("Barcelona", "Venice"),
        ("Paris", "Hamburg"),
        ("Paris", "Vilnius"),
        ("Paris", "Amsterdam"),
        ("Paris", "Florence"),
        ("Florence", "Amsterdam"),
        ("Vilnius", "Warsaw"),
        ("Barcelona", "Tallinn"),
        ("Paris", "Warsaw"),
        ("Tallinn", "Warsaw"),
        ("Amsterdam", "Tallinn"),
        ("Paris", "Tallinn"),
        ("Paris", "Barcelona"),
        ("Venice", "Hamburg"),
        ("Warsaw", "Hamburg"),
        ("Hamburg", "Salzburg"),
        ("Amsterdam", "Venice"),
    ]
    # Directed edges
    directed_edges = [
        ("Tallinn", "Vilnius"),  # from Tallinn to Vilnius
    ]
    adjacency: Dict[str, Set[str]] = {}
    def add_edge(a, b):
        adjacency.setdefault(a, set()).add(b)
    for a, b in undirected_pairs:
        add_edge(a, b)
        add_edge(b, a)
    for a, b in directed_edges:
        add_edge(a, b)
    return adjacency

def compute_itinerary():
    # Input variables: durations and constraints
    durations = {
        "Paris": 2,
        "Venice": 3,
        "Vilnius": 3,
        "Salzburg": 4,
        "Amsterdam": 2,
        "Barcelona": 5,
        "Hamburg": 4,
        "Florence": 5,
        "Tallinn": 2,
        "Warsaw": 4,
    }
    cities = [
        "Paris", "Barcelona", "Amsterdam", "Vilnius", "Warsaw",
        "Tallinn", "Florence", "Venice", "Hamburg", "Salzburg"
    ]
    total_days = 25
    adjacency = build_adjacency()

    # Hard constraints as required day sets
    required_days = {
        "Paris": {1, 2},
        "Hamburg": {19, 20, 21, 22},
        "Salzburg": {22, 23, 24, 25},
        "Tallinn": {11, 12},
    }
    # Overlap constraints (city must overlap with at least one day in window)
    overlap_windows = {
        "Barcelona": (2, 6),  # Meet friends between day 2 and 6
    }
    # Heuristic target start days for ordering
    target_start = {
        "Paris": 1,
        "Barcelona": 2,
        "Tallinn": 11,
        "Hamburg": 19,
        "Salzburg": 22,
    }

    # Pre-fix first, last-1, and last city due to tight windows
    first_city = "Paris"
    last_city = "Salzburg"
    second_last_city = "Hamburg"

    remaining = [c for c in cities if c not in (first_city, second_last_city, last_city)]

    # Helper to check required-day constraints
    def satisfies_required_days(city: str, start: int, end: int) -> bool:
        if city in required_days:
            req = required_days[city]
            for d in req:
                if not (start <= d <= end):
                    return False
        return True

    # Helper to check overlap window constraints
    def satisfies_overlap(city: str, start: int, end: int) -> bool:
        if city in overlap_windows:
            a, b = overlap_windows[city]
            # must overlap at least one day
            return not (end < a or start > b)
        return True

    # DFS to build order for positions 2..8 (since pos9=Hamburg, pos10=Salzburg)
    best_order = None

    # Pre-compute duration sum check to ensure that ending day is 25 automatically
    sum_durations = sum(durations[c] for c in cities)
    n_cities = len(cities)
    # Correct formula: with 1-day overlap between each pair, final end day is:
    # end_day = sum(durations) - (n_cities - 1)
    expected_last_day = sum_durations - (n_cities - 1)
    if expected_last_day != total_days:
        raise ValueError("Durations and city count cannot yield the requested total days with 1-day overlaps.")

    # Neighbor ordering heuristic
    def neighbor_sort_key(next_city: str, start_day: int) -> Tuple[int, int, str]:
        # Prefer cities with defined target start close to current start
        target = target_start.get(next_city, None)
        proximity = abs(start_day - target) if target is not None else 1000
        # Secondary: cities with constraints have priority
        constraint_priority = 0
        if next_city in required_days or next_city in overlap_windows:
            constraint_priority = -1
        return (proximity, constraint_priority, next_city)

    def dfs_build(current_path: List[str], ranges: Dict[str, Tuple[int, int]]):
        nonlocal best_order
        if best_order is not None:
            return  # found one valid solution
        # Determine next position index
        pos = len(current_path) + 1  # 1-indexed
        # Determine the last city and its end day to compute next start
        last_city_in_path = current_path[-1]
        s_last, e_last = ranges[last_city_in_path]

        if pos == 9:
            # Next must be Hamburg; verify adjacency and timing
            if second_last_city not in adjacency.get(last_city_in_path, set()):
                return
            # Compute Hamburg's range
            s_h = e_last
            e_h = s_h + durations[second_last_city] - 1
            # Check constraints for Hamburg
            if not (satisfies_required_days(second_last_city, s_h, e_h) and satisfies_overlap(second_last_city, s_h, e_h)):
                return
            # Now Salzburg must follow Hamburg and be last; verify adjacency and timing
            if last_city not in adjacency.get(second_last_city, set()):
                return
            # Compute Salzburg's range
            s_s = e_h
            e_s = s_s + durations[last_city] - 1
            if not (satisfies_required_days(last_city, s_s, e_s) and satisfies_overlap(last_city, s_s, e_s)):
                return
            # Build full order and finalize
            full_order = current_path + [second_last_city, last_city]
            final_ranges = dict(ranges)
            final_ranges[second_last_city] = (s_h, e_h)
            final_ranges[last_city] = (s_s, e_s)
            # Validate all constraints are met
            for c in cities:
                s, e = final_ranges[c]
                if not satisfies_required_days(c, s, e):
                    return
                if not satisfies_overlap(c, s, e):
                    return
            best_order = (full_order, final_ranges)
            return

        # Otherwise, choose the next city from remaining
        remaining_set = set(remaining) - set(current_path[1:])  # exclude those already used beyond first
        # Build candidate list considering adjacency
        candidates = []
        for c in remaining_set:
            if c in adjacency.get(last_city_in_path, set()):
                s_c = e_last
                e_c = s_c + durations[c] - 1
                # Early constraint pruning
                if not satisfies_required_days(c, s_c, e_c):
                    continue
                if not satisfies_overlap(c, s_c, e_c):
                    continue
                candidates.append((c, s_c, e_c))
        # Sort by heuristic
        candidates.sort(key=lambda x: neighbor_sort_key(x[0], x[1]))
        for c, s_c, e_c in candidates:
            new_ranges = dict(ranges)
            new_ranges[c] = (s_c, e_c)
            dfs_build(current_path + [c], new_ranges)

    # Initialize with first city
    initial_ranges = {first_city: (1, 1 + durations[first_city] - 1)}
    # Validate initial satisfies its constraints
    if not (satisfies_required_days(first_city, *initial_ranges[first_city]) and satisfies_overlap(first_city, *initial_ranges[first_city])):
        raise ValueError("Initial city does not satisfy constraints.")

    dfs_build([first_city], initial_ranges)

    if best_order is None:
        raise RuntimeError("No valid itinerary found under given constraints.")

    order, ranges = best_order

    # Construct itinerary output with overlapping day ranges
    itinerary = []
    for c in order:
        s, e = ranges[c]
        itinerary.append({"day_range": f"Day {s}-{e}", "place": c})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))
import json
from typing import Dict, List, Tuple, Set, Optional

def build_flight_graph(undirected_edges: List[Tuple[str, str]], directed_edges: List[Tuple[str, str]]) -> Dict[str, Set[str]]:
    graph: Dict[str, Set[str]] = {}
    def add_edge(a: str, b: str):
        graph.setdefault(a, set()).add(b)
        graph.setdefault(b, set())
    for a, b in undirected_edges:
        add_edge(a, b)
        add_edge(b, a)
    for a, b in directed_edges:
        graph.setdefault(a, set()).add(b)
        graph.setdefault(b, set())
    return graph

def overlaps(a_start: int, a_end: int, b_start: int, b_end: int) -> bool:
    return not (a_end < b_start or a_start > b_end)

def includes_range(s_start: int, s_end: int, w_start: int, w_end: int) -> bool:
    return s_start <= w_start and s_end >= w_end

def compute_start_day(order: List[str], durations: Dict[str, int]) -> int:
    # Start day for next city with overlap rule (start_next = end_prev)
    # For first city (len(order) == 0), start = 1
    return 1 + sum(durations[c] for c in order) - len(order)

def day_range_for(order: List[str], candidate: str, durations: Dict[str, int]) -> Tuple[int, int]:
    s = compute_start_day(order, durations)
    e = s + durations[candidate] - 1
    return s, e

def windows_ok(city: str, start: int, end: int,
               include_windows: Dict[str, Tuple[int, int]],
               overlap_windows: Dict[str, Tuple[int, int]]) -> bool:
    if city in include_windows:
        a, b = include_windows[city]
        if not includes_range(start, end, a, b):
            return False
    if city in overlap_windows:
        a, b = overlap_windows[city]
        if not overlaps(start, end, a, b):
            return False
    return True

def search_itinerary(cities: List[str],
                     durations: Dict[str, int],
                     graph: Dict[str, Set[str]],
                     include_windows: Dict[str, Tuple[int, int]],
                     overlap_windows: Dict[str, Tuple[int, int]],
                     total_days: int) -> Optional[List[str]]:
    # Fix Brussels as last city due to include window [26,27] and 2-day duration
    last_city = "Brussels"
    assert last_city in cities

    # Geneva must include [1,4] fully, which with duration 4 implies start=Day 1, thus must be first
    first_city = "Geneva"
    if first_city not in cities:
        return None

    remaining = [c for c in cities if c not in (first_city, last_city)]
    # For deterministic search order
    remaining.sort()

    def backtrack(order: List[str], remaining_cities: List[str]) -> Optional[List[str]]:
        j = len(order)
        # If all but last city placed, try to place Brussels
        if len(remaining_cities) == 0:
            # place last: Brussels
            # Check flight from previous to Brussels
            if j > 0 and last_city not in graph.get(order[-1], set()):
                return None
            s, e = day_range_for(order, last_city, durations)
            # Verify final end equals total_days and Brussels includes its window
            if e != total_days:
                return None
            if not windows_ok(last_city, s, e, include_windows, overlap_windows):
                return None
            return order + [last_city]

        # Place next city from remaining
        for idx, cand in enumerate(remaining_cities):
            # Flight constraint
            if j > 0 and cand not in graph.get(order[-1], set()):
                continue
            s, e = day_range_for(order, cand, durations)
            # Prune if day range invalid (outside 1..total_days)
            if s < 1 or e > total_days:
                continue
            # Window constraints
            if not windows_ok(cand, s, e, include_windows, overlap_windows):
                continue
            # Additional feasibility pruning:
            # If Venice must include [7,11], with duration=5 this implies exactly 7-11.
            # This is already enforced via include_windows.
            # Proceed
            next_order = order + [cand]
            next_remaining = remaining_cities[:idx] + remaining_cities[idx+1:]
            sol = backtrack(next_order, next_remaining)
            if sol is not None:
                return sol
        return None

    # Seed with first city, verifying its window
    s0, e0 = day_range_for([], first_city, durations)
    if not windows_ok(first_city, s0, e0, include_windows, overlap_windows):
        return None

    solution = backtrack([first_city], remaining)
    return solution

def build_itinerary(order: List[str], durations: Dict[str, int]) -> List[Dict[str, str]]:
    itinerary = []
    current_start = 1
    for city in order:
        start = current_start
        end = start + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
        current_start = end  # overlap day rule
    return itinerary

def main():
    # Input variables (trip constraints)
    total_days = 27
    cities = [
        "Istanbul", "Vienna", "Riga", "Brussels", "Madrid",
        "Vilnius", "Venice", "Geneva", "Munich", "Reykjavik"
    ]
    durations = {
        "Istanbul": 4,
        "Vienna": 4,
        "Riga": 2,
        "Brussels": 2,
        "Madrid": 4,
        "Vilnius": 4,
        "Venice": 5,
        "Geneva": 4,
        "Munich": 5,
        "Reykjavik": 2
    }
    # Flights (undirected "A and B" and directed "from A to B")
    undirected_edges = [
        ("Munich", "Vienna"),
        ("Istanbul", "Brussels"),
        ("Vienna", "Vilnius"),
        ("Madrid", "Munich"),
        ("Venice", "Brussels"),
        ("Riga", "Brussels"),
        ("Geneva", "Istanbul"),
        ("Munich", "Reykjavik"),
        ("Vienna", "Istanbul"),
        ("Riga", "Istanbul"),
        ("Reykjavik", "Vienna"),
        ("Venice", "Munich"),
        ("Madrid", "Venice"),
        ("Vilnius", "Istanbul"),
        ("Venice", "Vienna"),
        ("Venice", "Istanbul"),
        ("Munich", "Istanbul"),
        ("Reykjavik", "Brussels"),
        ("Vilnius", "Brussels"),
        ("Madrid", "Vienna"),
        ("Vienna", "Riga"),
        ("Geneva", "Vienna"),
        ("Madrid", "Brussels"),
        ("Vienna", "Brussels"),
        ("Geneva", "Brussels"),
        ("Geneva", "Madrid"),
        ("Munich", "Brussels"),
        ("Madrid", "Istanbul"),
        ("Geneva", "Munich"),
    ]
    directed_edges = [
        ("Reykjavik", "Madrid"),
        ("Riga", "Munich"),
        ("Vilnius", "Munich"),
        ("Riga", "Vilnius"),
    ]
    # Time windows
    include_windows = {
        "Geneva": (1, 4),   # must fully cover days 1-4
        "Venice": (7, 11),  # must fully cover days 7-11 (workshop span)
        "Brussels": (26, 27)  # must fully cover days 26-27 (wedding span)
    }
    overlap_windows = {
        "Vilnius": (20, 23)  # must overlap this range (meet friends)
    }

    # Build graph
    graph = build_flight_graph(undirected_edges, directed_edges)

    # Solve
    order = search_itinerary(cities, durations, graph, include_windows, overlap_windows, total_days)
    if order is None:
        raise RuntimeError("No valid itinerary found under the given constraints.")

    # Validate total coverage equals total_days
    itin = build_itinerary(order, durations)
    # Compute union coverage length (should be 27 due to overlap rule)
    # We can confirm last end day equals total_days
    last_range = itin[-1]["day_range"]
    last_end = int(last_range.split("-")[1])
    assert last_end == total_days, "Itinerary does not end on the required day."

    print(json.dumps({"itinerary": itin}, ensure_ascii=False))

if __name__ == "__main__":
    main()
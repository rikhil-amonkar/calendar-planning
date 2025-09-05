import json
from itertools import permutations
from typing import List, Dict, Tuple, Optional

def build_graph(edges: List[Tuple[str, str]]) -> Dict[str, set]:
    graph = {}
    for a, b in edges:
        graph.setdefault(a, set()).add(b)
        graph.setdefault(b, set()).add(a)
    return graph

def is_path_valid(path: List[str], graph: Dict[str, set]) -> bool:
    return all(path[i+1] in graph.get(path[i], set()) for i in range(len(path)-1))

def compute_itinerary_for_path(path: List[str], total_days: int, required_days: Dict[str, int]) -> Optional[List[Dict]]:
    n = len(path)
    segments = []
    # First city: Day 1 to required_days[first]
    start = 1
    end = required_days[path[0]]
    segments.append({"city": path[0], "start": start, "end": end})
    prev_end = end

    # Middle cities (if any): overlap with previous end day (flight day)
    for i in range(1, n-1):
        city = path[i]
        start = prev_end  # overlap flight day with previous city
        end = start + required_days[city] - 1
        segments.append({"city": city, "start": start, "end": end})
        prev_end = end

    # Last city: starts at previous end (overlap) and must end at total_days
    last_city = path[-1]
    start = prev_end
    end = total_days
    if (end - start + 1) != required_days[last_city]:
        return None  # Doesn't fit
    segments.append({"city": last_city, "start": start, "end": end})

    return segments

def validate_constraints(segments: List[Dict], total_days: int, required_days: Dict[str, int],
                         relatives_city: str, relatives_window: Tuple[int, int]) -> bool:
    # 1) Validate city-day counts with overlaps
    city_day_counts = {city: 0 for city in required_days}
    # Count days per city, inclusive ranges
    for seg in segments:
        city = seg["city"]
        city_day_counts[city] += (seg["end"] - seg["start"] + 1)
    if city_day_counts != required_days:
        return False

    # 2) Validate total days union is exactly total_days
    # Build day coverage set of any city (union)
    days_covered = set()
    for seg in segments:
        days_covered.update(range(seg["start"], seg["end"] + 1))
    if days_covered != set(range(1, total_days + 1)):
        return False

    # 3) Relatives window: must be in relatives_city on every day in window
    # This requires that the union of that city's segments includes the full window.
    rel_days = set(range(relatives_window[0], relatives_window[1] + 1))
    rel_covered = set()
    for seg in segments:
        if seg["city"] == relatives_city:
            rel_covered.update(range(seg["start"], seg["end"] + 1))
    if not rel_days.issubset(rel_covered):
        return False

    return True

def main():
    # Inputs (constraints)
    total_days = 17
    cities = ["Naples", "Vienna", "Vilnius"]
    required_days = {
        "Naples": 5,
        "Vienna": 7,
        "Vilnius": 7
    }
    direct_flights = [
        ("Naples", "Vienna"),
        ("Vienna", "Vilnius")
    ]
    # Must visit relatives in Naples between day 1 and day 5 inclusive
    relatives_city = "Naples"
    relatives_window = (1, 5)

    # Build flight graph
    graph = build_graph(direct_flights)

    # Number of flights required due to overlapping rule
    required_flights = sum(required_days.values()) - total_days
    if required_flights < 0:
        raise ValueError("Infeasible: required city-days sum is less than total trip days.")
    # We aim to minimize flights; with k cities visited once, minimal flights is k-1.
    min_flights = len(cities) - 1
    if required_flights != min_flights:
        raise ValueError("Infeasible under single-pass plan: required overlaps do not match minimal flights.")

    # Find valid Hamiltonian paths starting in the relatives city (must be in Naples on day 1)
    start_city = relatives_city
    other_cities = [c for c in cities if c != start_city]
    valid_paths = []
    for perm in permutations(other_cities):
        path = [start_city] + list(perm)
        if is_path_valid(path, graph):
            valid_paths.append(path)

    best_segments = None
    # Choose the first valid path that yields a feasible schedule satisfying all constraints
    for path in valid_paths:
        segments = compute_itinerary_for_path(path, total_days, required_days)
        if segments is None:
            continue
        if validate_constraints(segments, total_days, required_days, relatives_city, relatives_window):
            best_segments = segments
            break

    if best_segments is None:
        raise ValueError("No feasible itinerary found that satisfies all constraints.")

    # Format output
    itinerary = []
    for seg in best_segments:
        itinerary.append({
            "day_range": f"Day {seg['start']}-{seg['end']}",
            "place": seg["city"]
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
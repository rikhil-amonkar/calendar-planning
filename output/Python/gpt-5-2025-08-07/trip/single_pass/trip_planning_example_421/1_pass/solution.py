import json
from typing import List, Dict, Tuple, Optional

def build_adjacency(direct_flights: List[Tuple[str, str]]) -> Dict[str, List[str]]:
    adj = {}
    for a, b in direct_flights:
        adj.setdefault(a, []).append(b)
        adj.setdefault(b, []).append(a)
    # Sort neighbors for deterministic traversal
    for k in adj:
        adj[k] = sorted(set(adj[k]))
    return adj

def find_hamiltonian_path(adj: Dict[str, List[str]], start: str, end: str, all_cities: List[str]) -> Optional[List[str]]:
    n = len(all_cities)
    all_set = set(all_cities)

    def dfs(current: str, path: List[str], visited: set) -> Optional[List[str]]:
        if len(path) == n:
            if current == end:
                return path[:]
            return None

        # Explore neighbors; avoid going to end until it would complete the path
        for neighbor in adj.get(current, []):
            if neighbor == end and len(path) != n - 1:
                continue  # only allow going to 'end' as the final step
            if neighbor not in visited:
                visited.add(neighbor)
                path.append(neighbor)
                res = dfs(neighbor, path, visited)
                if res is not None:
                    return res
                path.pop()
                visited.remove(neighbor)
        return None

    return dfs(start, [start], {start})

def compute_itinerary(order: List[str], durations: Dict[str, int], total_days: int, anchors: Dict[str, Tuple[int, int]]) -> Optional[List[Tuple[str, int, int]]]:
    # We anchor the first city's start day using its anchor if provided; otherwise day 1.
    first_city = order[0]
    last_city = order[-1]

    # Determine anchored start for the first city
    if first_city in anchors:
        start_day = anchors[first_city][0]
        # Ensure duration matches anchor span for the first city if an anchor is provided
        if (anchors[first_city][1] - anchors[first_city][0] + 1) != durations[first_city]:
            return None
    else:
        start_day = 1  # default

    schedule = []
    current_start = start_day

    for i, city in enumerate(order):
        if i == 0:
            city_start = current_start
        else:
            # Travel on the last day of the previous city to create the 1-day overlap
            city_start = schedule[-1][2]
        city_end = city_start + durations[city] - 1
        schedule.append((city, city_start, city_end))

    # Validate total unique days using overlaps: unique coverage should be from min start to max end
    unique_start = min(s for _, s, _ in schedule)
    unique_end = max(e for _, _, e in schedule)
    if unique_start != 1:
        # Adjust to start at day 1 if possible by shifting everything
        shift = 1 - unique_start
        schedule = [(c, s + shift, e + shift) for (c, s, e) in schedule]
        unique_start = 1
        unique_end = max(e for _, _, e in schedule)

    if unique_end != total_days:
        # If end doesn't match total days but anchors require it, we fail; otherwise try shifting to end at total_days
        desired_shift = total_days - unique_end
        schedule = [(c, s + desired_shift, e + desired_shift) for (c, s, e) in schedule]
        unique_start = min(s for _, s, _ in schedule)
        unique_end = max(e for _, _, e in schedule)
        if unique_start != 1 or unique_end != total_days:
            return None

    # Validate anchors
    for city, (a_start, a_end) in anchors.items():
        # City must cover the entire anchor interval
        matched = next((s_e for s_e in schedule if s_e[0] == city), None)
        if not matched:
            return None
        _, s, e = matched
        if not (s <= a_start and e >= a_end and (e - s + 1) == durations[city]):
            return None

    # Validate adjacency is inherently respected by 'order' generation
    # Validate coverage contiguous from 1 to total_days (no gaps)
    # Because of overlap design, coverage spans continuously
    return schedule

def main():
    # Input variables (trip constraints)
    total_days = 20
    cities = ["Nice", "Dublin", "Krakow", "Lyon", "Frankfurt"]
    durations = {
        "Nice": 5,
        "Dublin": 7,
        "Krakow": 6,
        "Lyon": 4,
        "Frankfurt": 2,
    }
    # Anchors: city must include the full range
    anchors = {
        "Nice": (1, 5),        # visit relatives between day 1 and 5, and duration is 5
        "Frankfurt": (19, 20)  # meet friends between day 19 and 20, and duration is 2
    }
    direct_flights = [
        ("Nice", "Dublin"),
        ("Dublin", "Frankfurt"),
        ("Dublin", "Krakow"),
        ("Krakow", "Frankfurt"),
        ("Lyon", "Frankfurt"),
        ("Nice", "Frankfurt"),
        ("Lyon", "Dublin"),
        ("Nice", "Lyon"),
    ]

    # Basic feasibility check: sum(durations) - (number_of_transitions) must equal total_days
    n = len(cities)
    sum_durations = sum(durations[c] for c in cities)
    min_transitions = n - 1  # sequential visits
    unique_days_possible = sum_durations - min_transitions
    if unique_days_possible != total_days:
        raise ValueError("Infeasible: summed city days and overlaps cannot match total days.")

    # Build adjacency
    adj = build_adjacency(direct_flights)

    # Find an order/path starting at Nice and ending at Frankfurt that visits all cities exactly once
    start_city = "Nice"
    end_city = "Frankfurt"
    path = find_hamiltonian_path(adj, start_city, end_city, cities)
    if not path:
        raise ValueError("No valid visiting order satisfies direct flight constraints.")

    # Compute a concrete itinerary satisfying day anchors and overlaps
    schedule = compute_itinerary(path, durations, total_days, anchors)
    if not schedule:
        raise ValueError("Failed to compute a schedule that satisfies all constraints.")

    # Build JSON output
    itinerary = []
    for city, start, end in schedule:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
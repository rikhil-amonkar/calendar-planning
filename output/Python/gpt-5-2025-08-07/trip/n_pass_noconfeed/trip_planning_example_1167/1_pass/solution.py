import json
from typing import List, Dict, Tuple, Optional

def build_adjacency(cities: List[str], connections: List[str]) -> Dict[str, set]:
    adj = {c: set() for c in cities}
    for line in connections:
        line = line.strip()
        if line.lower().startswith("from "):
            # Directed edge: from A to B
            try:
                rest = line[5:]  # after 'from '
                a, b = rest.split(" to ")
                a = a.strip()
                b = b.strip()
                if a in adj and b in adj:
                    adj[a].add(b)
            except ValueError:
                pass  # Ignore malformed lines
        else:
            # Undirected edge: A and B
            if " and " in line:
                a, b = line.split(" and ")
                a = a.strip()
                b = b.strip()
                if a in adj and b in adj:
                    adj[a].add(b)
                    adj[b].add(a)
    return adj

def compute_day_ranges(order: List[str], durations: Dict[str, int]) -> Dict[str, Tuple[int, int]]:
    # Overlap by exactly 1 day between consecutive cities (travel day counts in both)
    # Start first city on day 1
    ranges = {}
    prev_end = None
    for i, city in enumerate(order):
        start = 1 if i == 0 else prev_end
        end = start + durations[city] - 1
        ranges[city] = (start, end)
        prev_end = end
    return ranges

def overlap(a: Tuple[int, int], b: Tuple[int, int]) -> bool:
    return not (a[1] < b[0] or b[1] < a[0])

def covers(container: Tuple[int, int], contained: Tuple[int, int]) -> bool:
    return container[0] <= contained[0] and container[1] >= contained[1]

def find_itinerary(
    cities: List[str],
    durations: Dict[str, int],
    adj: Dict[str, set],
    total_days: int,
    must_cover: Dict[str, Tuple[int, int]],
    must_overlap_constraints: Dict[str, Tuple[int, int]],
    preferred_order: List[str]
) -> Optional[List[str]]:
    n = len(cities)
    total_city_days = sum(durations[c] for c in cities)
    required_overlaps = n - 1
    if total_city_days - required_overlaps != total_days:
        return None  # Impossible to fit exactly with 1-day overlaps per flight

    preferred_index = {c: i for i, c in enumerate(preferred_order)}

    def dfs(path: List[str], prev_end: Optional[int], assigned_ranges: Dict[str, Tuple[int, int]], visited: set) -> Optional[List[str]]:
        if len(path) == n:
            # Validate final day reach
            last_city = path[-1]
            if assigned_ranges[last_city][1] != total_days:
                return None
            # Double-check all constraints
            for city in cities:
                s, e = assigned_ranges[city]
                if city in must_cover and not covers((s, e), must_cover[city]):
                    return None
                if city in must_overlap_constraints and not overlap((s, e), must_overlap_constraints[city]):
                    return None
            # Validate all flights are direct
            for i in range(1, n):
                if path[i] not in adj[path[i-1]]:
                    return None
            return path

        # Determine candidate next cities
        if not path:
            candidates = [c for c in cities if c not in visited]
        else:
            last = path[-1]
            candidates = [c for c in cities if c not in visited and c in adj[last]]

        # Sort candidates by preference to find a good solution quickly
        candidates.sort(key=lambda c: preferred_index.get(c, len(preferred_order)))

        for cand in candidates:
            # Compute day range for candidate
            start = 1 if prev_end is None else prev_end
            end = start + durations[cand] - 1

            # Early pruning: ensure we cannot exceed total days prematurely at the end
            # Not necessary here since end at final step is fixed to total_days.

            # Check constraints for this candidate
            if cand in must_cover:
                if not covers((start, end), must_cover[cand]):
                    continue
            if cand in must_overlap_constraints:
                if not overlap((start, end), must_overlap_constraints[cand]):
                    continue

            # Tentatively assign and recurse
            path.append(cand)
            visited.add(cand)
            assigned_ranges[cand] = (start, end)

            result = dfs(path, end, assigned_ranges, visited)
            if result is not None:
                return result

            # Backtrack
            path.pop()
            visited.remove(cand)
            assigned_ranges.pop(cand, None)

        return None

    return dfs([], None, {}, set())

def main():
    # Input variables (constraints)
    total_days = 21
    cities = [
        "Dublin",
        "Krakow",
        "Istanbul",
        "Venice",
        "Naples",
        "Brussels",
        "Mykonos",
        "Frankfurt"
    ]
    durations = {
        "Dublin": 5,
        "Krakow": 4,
        "Istanbul": 3,
        "Venice": 3,
        "Naples": 4,
        "Brussels": 2,
        "Mykonos": 4,
        "Frankfurt": 3
    }

    # Flight connections as given (mixture of undirected "A and B" and directed "from A to B")
    connections = [
        "Dublin and Brussels",
        "Mykonos and Naples",
        "Venice and Istanbul",
        "Frankfurt and Krakow",
        "Naples and Dublin",
        "Krakow and Brussels",
        "Naples and Istanbul",
        "Naples and Brussels",
        "Istanbul and Frankfurt",
        "from Brussels to Frankfurt",
        "Istanbul and Krakow",
        "Istanbul and Brussels",
        "Venice and Frankfurt",
        "Naples and Frankfurt",
        "Dublin and Krakow",
        "Venice and Brussels",
        "Naples and Venice",
        "Istanbul and Dublin",
        "Venice and Dublin",
        "Dublin and Frankfurt"
    ]
    adjacency = build_adjacency(cities, connections)

    # Special timing constraints
    must_cover = {
        # Must be in Dublin for the show from day 11 to day 15 (duration 5 forces exactly these days)
        "Dublin": (11, 15)
    }
    must_overlap_constraints = {
        # Must be in Istanbul on at least one day between 9 and 11
        "Istanbul": (9, 11),
        # Visit relatives in Mykonos between day 1 and day 4 (at least one day there)
        "Mykonos": (1, 4),
        # Meet friends in Frankfurt between day 15 and 17 (at least one day there)
        "Frankfurt": (15, 17)
    }

    # Heuristic preferred order to guide search
    preferred_order = ["Mykonos", "Naples", "Venice", "Istanbul", "Dublin", "Frankfurt", "Krakow", "Brussels"]

    order = find_itinerary(
        cities=cities,
        durations=durations,
        adj=adjacency,
        total_days=total_days,
        must_cover=must_cover,
        must_overlap_constraints=must_overlap_constraints,
        preferred_order=preferred_order
    )

    if order is None:
        result = {"itinerary": []}
    else:
        ranges = compute_day_ranges(order, durations)
        itinerary = []
        # Build output respecting the order found
        for city in order:
            start, end = ranges[city]
            itinerary.append({
                "day_range": f"Day {start}-{end}",
                "place": city
            })
        result = {"itinerary": itinerary}

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()
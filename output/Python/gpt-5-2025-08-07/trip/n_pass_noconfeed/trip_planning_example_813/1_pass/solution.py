import json
from itertools import permutations

def build_adjacency(edges):
    adj = {}
    for a, b in edges:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def compute_schedule_for_path(path, durations, total_days):
    # Build overlapping schedule: each transition overlaps by one day (flight day)
    schedule = []
    start_day = 1
    for i, city in enumerate(path):
        dur = durations[city]
        if i == 0:
            s = start_day
        else:
            # Overlap one day with previous city (flight day)
            s = schedule[-1][2]  # previous end day (overlap)
        e = s + dur - 1
        schedule.append((city, s, e))
    # Validate total days
    if schedule[-1][2] != total_days:
        return None
    return schedule

def satisfies_windows(schedule, windows):
    # windows: dict city -> constraints function or tuple specs
    # Here we enforce:
    # - London must include both days 9 and 10
    # - Stuttgart must be entirely within days 7-9 (i.e., exactly 7-9 since duration is 3)
    city_to_range = {city: (s, e) for city, s, e in schedule}
    # London: include both 9 and 10
    if "London" not in city_to_range:
        return False
    sL, eL = city_to_range["London"]
    if not (sL <= 9 <= eL and sL <= 10 <= eL):
        return False
    # Stuttgart: entirely within [7, 9]
    if "Stuttgart" not in city_to_range:
        return False
    sS, eS = city_to_range["Stuttgart"]
    if not (sS >= 7 and eS <= 9):
        return False
    return True

def find_itinerary(cities, durations, edges, total_days):
    adj = build_adjacency(edges)

    # Validate basic inputs
    if set(cities) != set(durations.keys()):
        raise ValueError("Cities and durations mismatch.")
    if sum(durations.values()) - (len(cities) - 1) != total_days:
        raise ValueError("Durations and overlap count do not sum to total_days.")

    # Direct flight check function
    def is_path_valid(path):
        return all(path[i+1] in adj[path[i]] for i in range(len(path)-1))

    # Endpoints must be degree-1 nodes to be ends in a Hamiltonian path.
    degrees = {c: len(adj.get(c, [])) for c in cities}
    endpoints = [c for c, d in degrees.items() if d == 1]
    # Expecting exactly two endpoints (Vilnius and Seville)
    if len(endpoints) != 2:
        # Fallback to try all permutations if degree info not as expected
        start_candidates = cities
    else:
        start_candidates = endpoints

    # DFS to build Hamiltonian path honoring direct flights and endpoints placement
    N = len(cities)
    target_end = set(endpoints) if len(endpoints) == 2 else set()

    def dfs(path, used):
        if len(path) == N:
            # If we know endpoints, ensure path ends at the other endpoint
            if target_end and path[-1] not in target_end:
                return None
            if not is_path_valid(path):
                return None
            schedule = compute_schedule_for_path(path, durations, total_days)
            if schedule and satisfies_windows(schedule, windows=None):
                return schedule
            return None

        last = path[-1]
        # Try neighbors first (prunes search space significantly)
        neighbors = sorted(adj[last])
        for nb in neighbors:
            if nb in used:
                continue
            # If nb is an endpoint and we are not at the last position, only allow it if it will be the final node
            if nb in target_end and len(path) != N-1:
                continue
            # Proceed if still potentially valid
            used.add(nb)
            schedule = dfs(path + [nb], used)
            if schedule:
                return schedule
            used.remove(nb)
        return None

    # Try building from each valid start candidate
    for start in start_candidates:
        # If endpoints defined, the start must be one of them
        if target_end and start not in target_end:
            continue
        sched = dfs([start], {start})
        if sched:
            return sched

    # Fallback: brute-force all permutations if DFS with endpoint hinting failed (very unlikely here)
    for perm in permutations(cities):
        if not is_path_valid(perm):
            continue
        sched = compute_schedule_for_path(perm, durations, total_days)
        if sched and satisfies_windows(sched, windows=None):
            return sched

    return None

def main():
    # Input variables (trip constraints)
    total_days = 17
    durations = {
        "Seville": 5,
        "Vilnius": 3,
        "Santorini": 2,
        "London": 2,
        "Stuttgart": 3,
        "Dublin": 3,
        "Frankfurt": 5
    }
    cities = list(durations.keys())

    edges = [
        ("Frankfurt", "Dublin"),
        ("Frankfurt", "London"),
        ("London", "Dublin"),
        ("Vilnius", "Frankfurt"),
        ("Frankfurt", "Stuttgart"),
        ("Dublin", "Seville"),
        ("London", "Santorini"),
        ("Stuttgart", "London"),
        ("Santorini", "Dublin")
    ]

    schedule = find_itinerary(cities, durations, edges, total_days)

    if not schedule:
        # Output a valid JSON with an empty itinerary to satisfy contract if no solution
        print(json.dumps({"itinerary": []}, ensure_ascii=False))
        return

    # Format output
    itinerary = []
    for city, s, e in schedule:
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
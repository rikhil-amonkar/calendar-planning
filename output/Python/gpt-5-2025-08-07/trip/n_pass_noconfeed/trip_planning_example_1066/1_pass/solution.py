import json
from collections import defaultdict

def build_adjacency(direct_flights):
    adj = defaultdict(set)
    for a, b in direct_flights:
        adj[a].add(b)
        adj[b].add(a)
    return adj

def compute_schedule(order, durations):
    # Given an ordered list of cities (with final city last), compute overlapping schedule:
    # Flight occurs on the last day of each city except the last, overlapping with the next city's first day.
    schedule = {}
    current_start = 1
    for i, city in enumerate(order):
        d = durations[city]
        end_day = current_start + d - 1
        schedule[city] = (current_start, end_day)
        # Next city starts on this end day (flight day overlap)
        current_start = end_day
    return schedule

def validate_schedule(schedule, constraints):
    # Friend constraint in Stuttgart between day 1 and 4 (inclusive)
    friend_city = constraints["friend_city"]
    friend_window = constraints["friend_window"]  # (start_day, end_day)
    s_start, s_end = schedule[friend_city]
    if s_end < friend_window[0] or s_start > friend_window[1]:
        return False

    # Conference: must be in Madrid on days 20 and 21 (inclusive)
    conf_city = constraints["conference_city"]
    conf_days = constraints["conference_days"]  # list or tuple of days
    c_start, c_end = schedule[conf_city]
    if not all(c_start <= day <= c_end for day in conf_days):
        return False

    # Total unique days should be exactly total_days
    all_starts = [v[0] for v in schedule.values()]
    all_ends = [v[1] for v in schedule.values()]
    trip_start = min(all_starts)
    trip_end = max(all_ends)
    if trip_start != 1 or trip_end != constraints["total_days"]:
        return False

    # Durations check
    for city, (start, end) in schedule.items():
        if (end - start + 1) != constraints["durations"][city]:
            return False

    return True

def find_itinerary(cities, durations, adj, constraints):
    n = len(cities)
    last_city = constraints["conference_city"]  # Must be last to guarantee presence on specific days
    others = [c for c in cities if c != last_city]

    # Quick feasibility check: sum(durations) must equal total_days + (n-1) due to overlaps on flight days
    flights_needed = n - 1
    if sum(durations.values()) != constraints["total_days"] + flights_needed:
        return None

    # DFS to find Hamiltonian path ending at last_city with direct flights between consecutive cities.
    best_order = None

    # Try Stuttgart first as starting city to help satisfy friend constraint quickly; then others.
    start_candidates = sorted(others, key=lambda c: (c != constraints["friend_city"], c))

    def dfs(path, used):
        nonlocal best_order
        if best_order is not None:
            return  # Found one feasible plan; stop at first
        if len(path) == n - 1:
            # Path covers all except last city; ensure last hop to last_city is allowed
            if path[-1] in adj and last_city in adj[path[-1]]:
                order = path + [last_city]
                schedule = compute_schedule(order, durations)
                if validate_schedule(schedule, constraints):
                    best_order = order
            return

        # Next candidates are neighbors of the current last city (to respect direct flights)
        if not path:
            next_cands = start_candidates
        else:
            last = path[-1]
            # Consider only neighbors that are not used yet and exist in the needed set (others)
            next_cands = sorted([c for c in adj[last] if c in others and c not in used])

        for nxt in next_cands:
            # Prune: if placing Mykonos too early with no way forward (it only connects to London/Madrid), ensure feasibility
            # If nxt is Mykonos and we are not at the position right before last, require that we can go to London next.
            path.append(nxt)
            used.add(nxt)
            # Mild forward-check: ensure that it's still possible to connect remaining nodes
            feasible = True
            if len(path) >= 2:
                # Ensure direct flight between last two nodes
                if path[-2] not in adj[path[-1]]:
                    feasible = False
            if feasible:
                dfs(path, used)
            path.pop()
            used.remove(nxt)

    dfs([], set())
    return best_order

def main():
    # Input variables (constraints)
    cities = [
        "Brussels",
        "Bucharest",
        "Stuttgart",
        "Mykonos",
        "Madrid",
        "Helsinki",
        "Split",
        "London",
    ]

    durations = {
        "Brussels": 4,
        "Bucharest": 3,
        "Stuttgart": 4,
        "Mykonos": 2,
        "Madrid": 2,
        "Helsinki": 5,
        "Split": 3,
        "London": 5,
    }

    direct_flights_pairs = [
        ("Helsinki", "London"),
        ("Split", "Madrid"),
        ("Helsinki", "Madrid"),
        ("London", "Madrid"),
        ("Brussels", "London"),
        ("Bucharest", "London"),
        ("Brussels", "Bucharest"),
        ("Bucharest", "Madrid"),
        ("Split", "Helsinki"),
        ("Mykonos", "Madrid"),
        ("Stuttgart", "London"),
        ("Helsinki", "Brussels"),
        ("Brussels", "Madrid"),
        ("Split", "London"),
        ("Stuttgart", "Split"),
        ("London", "Mykonos"),
    ]

    # Constraints
    constraints = {
        "total_days": 21,
        "conference_city": "Madrid",
        "conference_days": [20, 21],
        "friend_city": "Stuttgart",
        "friend_window": (1, 4),
        "durations": durations,
    }

    adj = build_adjacency(direct_flights_pairs)

    order = find_itinerary(cities, durations, adj, constraints)

    if not order:
        result = {"error": "No feasible itinerary found satisfying all constraints."}
        print(json.dumps(result))
        return

    schedule = compute_schedule(order, durations)
    # Build itinerary list in the requested format, following the computed order
    itinerary = []
    for city in order:
        start, end = schedule[city]
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
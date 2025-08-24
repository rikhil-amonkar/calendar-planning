import json
from collections import deque, defaultdict

def build_graph(direct_flights):
    graph = defaultdict(set)
    for a, b in direct_flights:
        graph[a].add(b)
        graph[b].add(a)
    return graph

def shortest_path(graph, start, goal):
    if start == goal:
        return [start]
    q = deque([start])
    prev = {start: None}
    while q:
        u = q.popleft()
        for v in graph[u]:
            if v not in prev:
                prev[v] = u
                if v == goal:
                    # reconstruct
                    path = [v]
                    while u is not None:
                        path.append(u)
                        u = prev[u]
                    path.reverse()
                    return path
                q.append(v)
    return None

def compute_itinerary(total_days, required_days, direct_flights, event_city, event_start, event_end):
    # Inputs validation
    cities_required = set(required_days.keys())
    if event_city not in cities_required:
        raise ValueError("Event city must be one of the required cities.")

    graph = build_graph(direct_flights)

    # Choose an order of visiting cities that:
    # - ends in event_city
    # - visits all required cities
    # - minimizes number of flights (transitions)
    candidates = []
    for start in cities_required:
        if start == event_city:
            continue
        path = shortest_path(graph, start, event_city)
        if path is None:
            continue
        if cities_required.issubset(set(path)):
            candidates.append(path)
    # If no single shortest path covers all, fallback: try to stitch a path via a simple heuristic
    if not candidates:
        # For small sets, attempt all permutations that end at event city and check if a path exists by concatenating shortest paths
        from itertools import permutations
        best = None
        best_len = float('inf')
        for order in permutations(cities_required - {event_city}):
            order = list(order) + [event_city]
            feasible = True
            stitched = [order[0]]
            for i in range(len(order)-1):
                sp = shortest_path(graph, order[i], order[i+1])
                if not sp:
                    feasible = False
                    break
                if i > 0:
                    # avoid duplicating the connecting node
                    stitched.extend(sp[1:])
                else:
                    stitched = sp[:]
            if feasible:
                # count flights as transitions where city changes
                flights = sum(1 for i in range(1, len(stitched)) if stitched[i] != stitched[i-1])
                if flights < best_len and cities_required.issubset(set(stitched)):
                    best_len = flights
                    best = stitched
        if best:
            candidates = [best]

    if not candidates:
        raise ValueError("No feasible visit order that covers all required cities using direct flights.")

    # Choose the candidate with minimal flights (fewest transitions)
    def flight_count(path):
        return sum(1 for i in range(1, len(path)) if path[i] != path[i-1])
    candidates.sort(key=lambda p: (flight_count(p), len(p)))
    visit_order = candidates[0]  # list like ['Naples', 'Milan', 'Seville']

    # Place the event city's segment to cover the event window with exactly the required days for that city
    req_event = required_days[event_city]
    event_len = event_end - event_start + 1
    if req_event < event_len:
        raise ValueError("Required days in event city are fewer than the event duration.")
    # To minimize extra time and align to end at event_end (safest when event_end == total_days)
    sev_start = event_end - req_event + 1
    sev_end = sev_start + req_event - 1
    if sev_start < 1 or sev_end > total_days or not (sev_start <= event_start and sev_end >= event_end):
        raise ValueError("Cannot place the event city segment within the trip bounds.")

    # Build segments backward from the event city using exact required days and shared flight days
    k = len(visit_order)
    segments = [None] * k  # each: (city, start, end) inclusive
    segments[-1] = (visit_order[-1], sev_start, sev_end)

    for idx in range(k - 2, -1, -1):
        city = visit_order[idx]
        next_start = segments[idx + 1][1]
        start = next_start - required_days[city] + 1
        end = next_start  # overlap on flight day
        segments[idx] = (city, start, end)
        if start < 1:
            raise ValueError("Segments cannot start before day 1; constraints incompatible.")

    # Ensure the timeline fits exactly from day 1 to total_days
    if segments[0][1] != 1 or segments[-1][2] != total_days:
        raise ValueError("Constructed segments do not exactly span the trip duration.")

    # Validate direct flight edges between consecutive cities
    for i in range(1, k):
        a = segments[i-1][0]
        b = segments[i][0]
        if a == b:
            continue
        if b not in graph[a]:
            raise ValueError(f"No direct flight between {a} and {b} for transition.")

    # Validate day counts per city and event coverage
    city_days = {c: set() for c in cities_required}
    for city, start, end in segments:
        for d in range(start, end + 1):
            city_days[city].add(d)

    # Check each city's required days
    for c, req in required_days.items():
        if len(city_days[c]) != req:
            raise ValueError(f"City {c} has {len(city_days[c])} days, required {req}.")

    # Check event coverage
    for d in range(event_start, event_end + 1):
        if d not in city_days[event_city]:
            raise ValueError("Event days are not fully covered in the event city.")

    # Check every day is covered by at least one city
    covered = set().union(*city_days.values())
    if covered != set(range(1, total_days + 1)):
        # Because flight days count for both, coverage should be complete
        missing = [d for d in range(1, total_days + 1) if d not in covered]
        if missing:
            raise ValueError(f"Some days are not covered: {missing}")

    # Format itinerary
    itinerary = []
    for city, start, end in segments:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    return {"itinerary": itinerary}


if __name__ == "__main__":
    # Input variables (can be modified)
    total_days = 12
    required_days = {
        "Naples": 3,
        "Seville": 4,
        "Milan": 7
    }
    direct_flights = [
        ("Milan", "Seville"),
        ("Naples", "Milan")
    ]
    event_city = "Seville"
    event_start = 9
    event_end = 12

    result = compute_itinerary(total_days, required_days, direct_flights, event_city, event_start, event_end)
    print(json.dumps(result, ensure_ascii=False))
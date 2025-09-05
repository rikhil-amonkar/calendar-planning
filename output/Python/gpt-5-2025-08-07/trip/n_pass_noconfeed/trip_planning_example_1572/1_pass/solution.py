import json
from collections import defaultdict, deque

def build_graph(edges):
    g = defaultdict(set)
    for a, b in edges:
        g[a].add(b)
        g[b].add(a)
    return g

def shortest_path_length(graph, start, goal):
    if start == goal:
        return 0
    visited = {start}
    q = deque([(start, 0)])
    while q:
        node, dist = q.popleft()
        for nei in graph[node]:
            if nei == goal:
                return dist + 1
            if nei not in visited:
                visited.add(nei)
                q.append((nei, dist + 1))
    return float('inf')

def can_reach_anchor_in_time(graph, candidate, next_anchor_city, days_left_before_anchor):
    if next_anchor_city is None:
        return True
    sp = shortest_path_length(graph, candidate, next_anchor_city)
    return sp <= days_left_before_anchor

def select_candidate(day, current_city, remaining, graph, next_anchor_day, next_anchor_city, forbid_cities=None):
    forbid_cities = forbid_cities or set()

    candidates = []
    # Option to stay
    if remaining[current_city] > 0 and current_city not in forbid_cities:
        candidates.append(current_city)

    # Move to neighbor cities with remaining > 0
    for nei in graph[current_city]:
        if remaining[nei] > 0 and nei not in forbid_cities:
            candidates.append(nei)

    # If we are on the last day before an anchor, restrict to cities that can reach the anchor directly next day
    if next_anchor_day is not None and day == next_anchor_day - 1:
        candidates = [c for c in candidates if (c == next_anchor_city) or (next_anchor_city in graph[c])]

    # Additional feasibility check: can reach anchor in time from candidate
    days_left_before_anchor = (next_anchor_day - day) if next_anchor_day is not None else None
    filtered = []
    for c in candidates:
        if next_anchor_day is None:
            filtered.append(c)
        else:
            if can_reach_anchor_in_time(graph, c, next_anchor_city, days_left_before_anchor):
                filtered.append(c)

    # Sort candidates by:
    # - remaining days (desc)
    # - whether has direct edge to next anchor (True first)
    # - alphabetical name for determinism
    def has_direct_to_anchor(c):
        if next_anchor_city is None:
            return False
        return next_anchor_city in graph[c] or c == next_anchor_city

    filtered = list(set(filtered))  # unique
    filtered.sort(key=lambda c: (-remaining[c], -int(has_direct_to_anchor(c)), c))
    return filtered

def fill_segment(schedule, start_day, end_day_excl, graph, remaining, next_anchor_day=None, next_anchor_city=None, hard_forbid=None):
    # hard_forbid: mapping day -> set(cities) not allowed that day
    hard_forbid = hard_forbid or {}
    for day in range(start_day, end_day_excl):
        # If already prefilled (anchor), just continue
        if schedule[day] is not None:
            continue

        current_city = schedule[day - 1]
        forbid = hard_forbid.get(day, set())

        candidates = select_candidate(day, current_city, remaining, graph, next_anchor_day, next_anchor_city, forbid_cities=forbid)
        chosen = None
        for c in candidates:
            # Additional lookahead feasibility: if day is the last overall day (23),
            # ensure that assigning c uses the last remaining day exactly
            chosen = c
            break

        if chosen is None:
            # As a fallback, if no candidate due to strict constraints, try any neighbor with remaining > 0 ignoring anchor feasibility
            neighbors = [n for n in list(graph[current_city]) + [current_city] if remaining[n] > 0 and n not in forbid]
            neighbors.sort(key=lambda c: (-remaining[c], c))
            if neighbors:
                chosen = neighbors[0]
            else:
                # This should not happen with sensible inputs; raise to signal failure
                raise RuntimeError(f"No feasible city to assign on day {day} from {current_city}")

        schedule[day] = chosen
        remaining[chosen] -= 1

def group_itinerary(schedule):
    # schedule is 1-based list of city per day
    res = []
    start = 1
    current = schedule[1]
    for d in range(2, len(schedule)):
        if schedule[d] != current:
            res.append({"day_range": f"Day {start}-{d-1}", "place": current})
            start = d
            current = schedule[d]
    # last segment
    res.append({"day_range": f"Day {start}-{len(schedule)-1}", "place": current})
    return res

def compute_presence(schedule):
    # presence per day per city: if day d city differs from day d-1 city, both count
    presence = defaultdict(set)
    for d in range(1, len(schedule)):
        c = schedule[d]
        presence[d].add(c)
        if d > 1:
            prev = schedule[d-1]
            if prev != c:
                presence[d].add(prev)
    return presence

def validate_events(presence, event_windows):
    for city, (start, end) in event_windows.items():
        for d in range(start, end+1):
            if city not in presence[d]:
                return False
    return True

def main():
    # Inputs
    total_days = 23
    cities = [
        "Berlin", "Paris", "Riga", "Stockholm", "Zurich",
        "Nice", "Seville", "Milan", "Lyon", "Naples"
    ]
    desired_days = {
        "Lyon": 3,
        "Paris": 5,
        "Riga": 2,
        "Berlin": 2,
        "Stockholm": 3,
        "Zurich": 5,
        "Nice": 2,
        "Seville": 3,
        "Milan": 3,
        "Naples": 4
    }
    # Direct flights (undirected)
    direct_pairs = [
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

    # Events: city -> (start_day, end_day)
    event_windows = {
        "Berlin": (1, 2),      # wedding
        "Nice": (12, 13),      # workshop
        "Stockholm": (20, 22)  # annual show
    }

    # Build graph
    graph = build_graph(direct_pairs)

    # Compute scaled desired targets to 23 total days
    sum_desired = sum(desired_days[c] for c in cities)
    scale = total_days / sum_desired
    scaled = {c: round(desired_days[c] * scale) for c in cities}

    # Base allocations: at least 1 day per city, but ensure anchors
    base = {c: 1 for c in cities}
    # Ensure Berlin for days 1-2, Nice for days 12-13, Stockholm for 2 end-of-day days total (we'll ensure presence covers 3 days)
    base["Berlin"] = max(base["Berlin"], 2)
    base["Nice"] = max(base["Nice"], 2)
    base["Stockholm"] = max(base["Stockholm"], 2)

    sum_base = sum(base.values())
    extras = total_days - sum_base

    # Deficits relative to scaled
    deficits = {c: max(0, scaled.get(c, 0) - base[c]) for c in cities}

    # Distribute extras greedily by deficit, then by degree (more connected cities preferred), then alphabetical
    degrees = {c: len(graph[c]) for c in cities}
    order = sorted(cities, key=lambda c: (-deficits[c], -degrees[c], c))
    alloc = base.copy()
    idx = 0
    while extras > 0 and any(deficits[c] > 0 for c in cities):
        c = order[idx % len(order)]
        if deficits[c] > 0:
            alloc[c] += 1
            deficits[c] -= 1
            extras -= 1
        idx += 1
    # If still extras left (due to rounding), allocate to most connected cities that help connectivity
    if extras > 0:
        order2 = sorted(cities, key=lambda c: (-degrees[c], c))
        i2 = 0
        while extras > 0:
            c = order2[i2 % len(order2)]
            alloc[c] += 1
            extras -= 1
            i2 += 1

    # Anchors
    anchors = {
        1: "Berlin",
        12: "Nice",
        21: "Stockholm"
    }

    # Initialize schedule (1-based index)
    schedule = [None] * (total_days + 1)

    # Prefill anchor blocks: Berlin days 1-2, Nice days 12-13, Stockholm day 21 (day 20 will be placed to Stockholm if feasible)
    schedule[1] = "Berlin"
    schedule[2] = "Berlin"
    alloc["Berlin"] -= 2

    # Pre-Nice segment: fill days 3..11 to be able to reach Nice on day 12
    fill_segment(schedule, 3, 12, graph, alloc, next_anchor_day=12, next_anchor_city="Nice", hard_forbid={})

    # Place Nice for days 12-13
    schedule[12] = "Nice"
    alloc["Nice"] -= 1
    schedule[13] = "Nice"
    alloc["Nice"] -= 1

    # Post-Nice to pre-Stockholm: fill days 14..20 with anchor day 21 as Stockholm
    # Forbid choosing Stockholm before day 20 to reserve its 2 days for day 20 and 21 if feasible
    hard_forbid_mid = {d: {"Stockholm"} for d in range(14, 20)}
    fill_segment(schedule, 14, 21, graph, alloc, next_anchor_day=21, next_anchor_city="Stockholm", hard_forbid=hard_forbid_mid)

    # Place Stockholm on day 21
    schedule[21] = "Stockholm"
    alloc["Stockholm"] -= 1

    # Last segment: days 22..23, no anchor.
    # For reachability, ensure that at day 22 we pick a city that has a neighbor with remaining > 0 for day 23.
    # We'll implement simple two-day lookahead in candidate selection inside custom logic here.
    for day in range(22, 24):
        if schedule[day] is not None:
            continue
        current_city = schedule[day - 1]

        # Build candidate list (include stay and neighbors)
        cands = []
        if alloc[current_city] > 0:
            cands.append(current_city)
        for nei in graph[current_city]:
            if alloc[nei] > 0:
                cands.append(nei)
        cands = list(set(cands))
        # Sort by remaining desc then degree then alphabetical
        cands.sort(key=lambda c: (-alloc[c], -len(graph[c]), c))

        chosen = None
        for c in cands:
            if day == 22:
                # ensure that there exists at least one city with remaining > 0 that is reachable in 1 step from c for day 23
                ok_next = False
                # Option to stay if remaining after decrement > 0
                if alloc[c] - 1 > 0:
                    ok_next = True
                else:
                    for nei2 in graph[c]:
                        if alloc[nei2] > 0:
                            ok_next = True
                            break
                if not ok_next:
                    continue
            chosen = c
            break

        if chosen is None:
            # Fallback: pick any neighbor, even if it causes overuse (shouldn't happen with consistent alloc)
            neighbors = [n for n in [current_city] + list(graph[current_city])]
            neighbors.sort()
            chosen = neighbors[0]

        schedule[day] = chosen
        alloc[chosen] -= 1

    # If any remaining allocations not used (due to rounding/greedy), try to place them by adjusting last days if possible
    # but ensure schedule days remain 1..23
    unused = {c: k for c, k in alloc.items() if k != 0}
    # We expect all to be zero
    # Validate presence for event windows
    presence = compute_presence(schedule)
    valid = validate_events(presence, event_windows)

    # If events not valid, attempt simple fix: if Stockholm not present on day 22, force day 22 to be a flight from Stockholm by setting day 22 destination to a city directly connected to Stockholm with remaining >= 0
    if not valid:
        # specific fix for Stockholm 20-22
        sw = event_windows["Stockholm"]
        d20, d22 = sw[0], sw[1]
        # if day 21 not Stockholm, force it
        if schedule[21] != "Stockholm":
            schedule[21] = "Stockholm"
        # ensure day 22 departs from Stockholm
        if schedule[21] == "Stockholm" and "Stockholm" not in presence[22]:
            # Set day 22 dest to a neighbor of Stockholm (prefer one already scheduled on day 22 to keep alloc consistent)
            stok_neighbors = sorted(list(graph["Stockholm"]))
            for n in stok_neighbors:
                schedule[22] = n
                break
        presence = compute_presence(schedule)
        valid = validate_events(presence, event_windows)

    # Build itinerary
    itinerary = group_itinerary(schedule)

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
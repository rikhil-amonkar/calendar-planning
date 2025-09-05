import json

def parse_flights(text):
    # Build directed adjacency from flight description text
    adj = {}
    def add_edge(a, b):
        adj.setdefault(a, set()).add(b)

    items = [itm.strip() for itm in text.strip().split(",")]
    for raw in items:
        if not raw:
            continue
        s = raw.strip()
        if s.endswith("."):
            s = s[:-1].strip()
        if s.lower().startswith("from "):
            # from X to Y
            s2 = s[5:].strip()  # remove 'from '
            if " to " not in s2:
                continue
            a, b = [x.strip() for x in s2.split(" to ", 1)]
            add_edge(a, b)
        elif " and " in s:
            a, b = [x.strip() for x in s.split(" and ", 1)]
            add_edge(a, b)
            add_edge(b, a)
    return adj

def plan_itinerary(cities, durations, windows, adj, total_days=30):
    # Model:
    # - Pointer p starts at day 1 (arrival day of the first city).
    # - Placing a city with duration d advances pointer by (d-1): p = p + (d - 1).
    # - Consecutive cities overlap on the boundary day (e.g., A: Day 1-5, B: Day 5-...).
    # - For any window city W with window [arr, dep], we require arrival day == arr and dep - arr + 1 == duration.
    # - Directed edge must exist from previous city to next city.
    # - Use all cities exactly once; final pointer must equal total_days.

    all_cities = list(cities)
    add = {c: durations[c] - 1 for c in all_cities}

    # Validate windows match durations and build arrival map
    win_arr = {}
    for c, (arr, dep) in windows.items():
        if c not in durations:
            return None
        if dep - arr + 1 != durations[c]:
            return None
        win_arr[c] = arr

    # Sanity: overall sum of (d-1) must match trip length (total_days - 1)
    total_add = sum(add.values())
    if total_add != total_days - 1:
        return None

    # Bitset subset-sum feasibility for pruning to next window arrival
    def can_reach_exact_gap(values, target):
        # values: list of non-negative ints
        # Return True if some subset sums to target
        bitset = 1  # bit 0 set
        for v in values:
            bitset |= (bitset << v)
        return (bitset >> target) & 1 == 1

    # DFS search
    N = len(all_cities)
    used = set()
    order = []  # list of cities in order
    ranges = []  # list of (city, start_day, end_day)

    def has_edge(a, b):
        if a is None:
            return True
        return b in adj.get(a, set())

    # For consistent exploration, but not strictly necessary
    city_order = sorted(all_cities)

    def dfs(prev, p):
        # p is the current pointer (arrival day of next city to place)
        if len(order) == N:
            # All cities placed; must end exactly at total_days
            return p == total_days

        # If any window city was missed (its arrival < p and not yet used), fail early
        for c, arr in win_arr.items():
            if c not in used and arr < p:
                return False

        # Determine if a window city is forced now
        forced = None
        for c, arr in win_arr.items():
            if c not in used and arr == p:
                forced = c
                break

        # Build candidate list
        if forced is not None:
            candidates = [forced]
        else:
            candidates = []
            for c in city_order:
                if c in used:
                    continue
                # If this city has a window, we can only place it exactly at its arrival
                if c in win_arr and win_arr[c] != p:
                    continue
                candidates.append(c)

        # Try candidates
        for c in candidates:
            if not has_edge(prev, c):
                continue

            p2 = p + add[c]  # new pointer after placing c

            # Prune against the next upcoming window (smallest arrival among unused windows)
            upcoming_arrivals = [win_arr[w] for w in win_arr if w not in used and w != c]
            next_arr = min(upcoming_arrivals) if upcoming_arrivals else None

            # If there is an upcoming window earlier than we finish this city, we may overshoot
            if next_arr is not None and p2 > next_arr:
                continue

            # If we are before the next window, ensure we can exactly reach that arrival
            if next_arr is not None and p2 < next_arr:
                # We can only use non-window cities to fill up to the next window arrival
                remaining_nonwindow = [
                    add[x]
                    for x in all_cities
                    if x not in used and x != c and x not in win_arr
                ]
                gap = next_arr - p2
                if gap < 0 or not can_reach_exact_gap(remaining_nonwindow, gap):
                    continue

            # Place city c
            start_day = p
            end_day = p + durations[c] - 1
            used.add(c)
            order.append(c)
            ranges.append((c, start_day, end_day))

            if dfs(c, p2):
                return True

            # Backtrack
            used.remove(c)
            order.pop()
            ranges.pop()

        return False

    ok = dfs(prev=None, p=1)
    if not ok:
        return None

    # Build output
    out = []
    for city, start, end in ranges:
        out.append({"day_range": f"Day {start}-{end}", "place": city})
    return out

def main():
    total_days = 30
    cities = [
        "Santorini",
        "Krakow",
        "Paris",
        "Vilnius",
        "Munich",
        "Geneva",
        "Amsterdam",
        "Budapest",
        "Split",
    ]
    durations = {
        "Santorini": 5,
        "Krakow": 5,
        "Paris": 5,
        "Vilnius": 3,
        "Munich": 5,
        "Geneva": 2,
        "Amsterdam": 4,
        "Budapest": 5,
        "Split": 4,
    }
    windows = {
        # arrival, departure (inclusive)
        "Paris": (11, 15),
        "Krakow": (18, 22),
        "Santorini": (25, 29),
    }
    flights_text = """
    Paris and Krakow, Paris and Amsterdam, Paris and Split, from Vilnius to Munich, Paris and Geneva,
    Amsterdam and Geneva, Munich and Split, Split and Krakow, Munich and Amsterdam, Budapest and Amsterdam,
    Split and Geneva, Vilnius and Split, Munich and Geneva, Munich and Krakow, from Krakow to Vilnius,
    Vilnius and Amsterdam, Budapest and Paris, Krakow and Amsterdam, Vilnius and Paris, Budapest and Geneva,
    Split and Amsterdam, Santorini and Geneva, Amsterdam and Santorini, Munich and Budapest, Munich and Paris.
    """

    adj = parse_flights(flights_text)

    itinerary = plan_itinerary(set(cities), durations, windows, adj, total_days=total_days)
    if itinerary is None:
        output = {"itinerary": []}
    else:
        output = {"itinerary": itinerary}

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()
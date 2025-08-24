import json
from collections import defaultdict

def build_graph():
    # Directed adjacency based on provided direct flights
    edges = defaultdict(set)
    def add_bidirectional(a, b):
        edges[a].add(b)
        edges[b].add(a)
    def add_directed(a, b):
        edges[a].add(b)

    add_bidirectional("Hamburg", "Frankfurt")
    add_bidirectional("Naples", "Mykonos")
    add_bidirectional("Hamburg", "Porto")
    add_directed("Hamburg", "Geneva")  # directed only Hamburg -> Geneva
    add_bidirectional("Mykonos", "Geneva")
    add_bidirectional("Frankfurt", "Geneva")
    add_bidirectional("Frankfurt", "Porto")
    add_bidirectional("Geneva", "Porto")
    add_bidirectional("Geneva", "Manchester")
    add_bidirectional("Naples", "Manchester")
    add_bidirectional("Frankfurt", "Naples")
    add_bidirectional("Frankfurt", "Manchester")
    add_bidirectional("Naples", "Geneva")
    add_bidirectional("Porto", "Manchester")
    add_bidirectional("Hamburg", "Manchester")
    return edges

def compute_itinerary():
    total_days = 18
    cities = ["Porto", "Geneva", "Frankfurt", "Hamburg", "Mykonos", "Naples", "Manchester"]
    city_index = {c: i for i, c in enumerate(cities)}

    # Minimum days (presence counts) per city
    min_days = {
        "Porto": 2,
        "Geneva": 3,
        "Mykonos": 3,
        "Manchester": 4,
        "Hamburg": 5,
        "Naples": 5,
        "Frankfurt": 2,
    }

    # Required presences by day (inclusive). If required on a day, must be present in that city that day.
    required_by_day = {
        5: {"Frankfurt"},
        6: {"Frankfurt"},
        15: {"Manchester"},
        16: {"Manchester"},
        17: {"Manchester"},
        18: {"Manchester"},
    }

    # Mykonos meeting window (at least one presence day)
    mykonos_window = (10, 12)

    # Build flight graph
    graph = build_graph()

    # Start city (choose Porto as a reasonable starting point consistent with staying there 2 days)
    start_city = "Porto"

    # DFS with pruning to minimize number of flight days
    best_solution = {
        "flights": float("inf"),
        "presence_by_day": None,
        "moves": None,  # list of (day, from, to or None)
        "start_city": start_city,
    }

    # For memoization: state -> minimal flights used reached; state: (day, current_city, counts_tuple, mykonos_hit)
    # counts tuple are remaining required days per city (non-negative)
    from functools import lru_cache

    def remaining_counts_tuple(counts):
        tup = []
        for c in cities:
            rem = max(0, min_days[c] - counts[c])
            tup.append(rem)
        return tuple(tup)

    # Pre-calc days left information to rough prune feasibility (upper bound of additional presence per city)
    def feasible(counts, day):
        # For each city, remaining possible presence is at most remaining days (since can be present at most once per day)
        days_left = total_days - day + 1
        for c in cities:
            needed = max(0, min_days[c] - counts[c])
            if needed > days_left:
                return False
        return True

    def mykonos_window_satisfied(presence_by_day, up_to_day):
        start, end = mykonos_window
        if up_to_day < start:
            return None  # unknown yet
        # Check presence in window intersections with [1..up_to_day]
        lo = start
        hi = min(end, up_to_day)
        for d in range(lo, hi + 1):
            if "Mykonos" in presence_by_day[d]:
                return True
        if up_to_day > end:
            return False  # window passed without presence
        return None  # not decided yet

    @lru_cache(maxsize=None)
    def memo_key(day, current_city, rem_counts_tuple, myk_flag):
        # Not used directly; lru_cache expects function, not key building; keep as placeholder
        return (day, current_city, rem_counts_tuple, myk_flag)

    # We will implement our own visited dict for pruning
    visited = {}

    def dfs(day, current_city, counts, presence_by_day, moves, flights_used):
        nonlocal best_solution

        # Add presence for current day (current city is always present)
        if day > total_days:
            # Completed all days; check final constraints
            # Check min days
            for c in cities:
                if counts[c] < min_days[c]:
                    return
            # Check Mykonos window satisfied
            mw = mykonos_window_satisfied(presence_by_day, total_days)
            if mw is False:
                return
            # Ensure all 7 cities visited at least once (presence > 0)
            for c in cities:
                if c not in set().union(*presence_by_day[1:]):  # shouldn't happen
                    return
            # Record as candidate
            if flights_used < best_solution["flights"]:
                best_solution = {
                    "flights": flights_used,
                    "presence_by_day": [set(s) for s in presence_by_day],
                    "moves": list(moves),
                    "start_city": moves[0][1] if moves else current_city,
                }
            return

        # Prune if already worse than best
        if flights_used >= best_solution["flights"]:
            return

        # Make a local copy to update today's presence and counts
        if current_city not in presence_by_day[day]:
            presence_by_day[day].add(current_city)
            counts[current_city] += 1
            added_current = True
        else:
            added_current = False

        # Check required presence today
        req_today = required_by_day.get(day, set())
        # We'll determine possible moves based on required presence
        # If required city is not current city, must fly to it today (if possible)
        forced_destination = None
        if req_today:
            for req_city in req_today:
                if req_city != current_city:
                    # Must fly to req_city today
                    forced_destination = req_city
                    break
                # else if current city equals required, no force from this constraint
        # Also, we cannot violate requirement: if forced_destination is set and there's no direct flight
        # from current_city to forced_destination, path is invalid
        if forced_destination is not None:
            if forced_destination not in graph[current_city]:
                # Undo today's presence count before returning
                if added_current:
                    counts[current_city] -= 1
                    presence_by_day[day].remove(current_city)
                return

        # Feasibility prune for remaining days
        if not feasible(counts, day):
            if added_current:
                counts[current_city] -= 1
                presence_by_day[day].remove(current_city)
            return

        # Mykonos window prune (if window passed without Mykonos presence)
        mw = mykonos_window_satisfied(presence_by_day, day)
        if mw is False:
            if added_current:
                counts[current_city] -= 1
                presence_by_day[day].remove(current_city)
            return

        # Memoization/pruning by state
        rem_tuple = remaining_counts_tuple(counts)
        # For mykonos flag in memo key, we just encode 0/1/2: 0=not yet determined,1=met,2=failed (we already returned on failed)
        if mw is None:
            myk_flag = 0
        elif mw is True:
            myk_flag = 1
        else:
            myk_flag = 2
        state_key = (day, current_city, rem_tuple, myk_flag)
        prev_best_flights = visited.get(state_key, None)
        if prev_best_flights is not None and flights_used >= prev_best_flights:
            # We've been in this state with equal or fewer flights; prune
            if added_current:
                counts[current_city] -= 1
                presence_by_day[day].remove(current_city)
            return
        visited[state_key] = flights_used

        # Build move options: either no flight, or one flight to a neighbor
        options = []

        # If there's a forced destination due to required presence, only that one flight option is allowed (unless current city already required)
        if forced_destination is not None and forced_destination != current_city:
            options.append(("flight", forced_destination))
        else:
            # Option: no flight
            options.append(("stay", None))
            # Flight options to any neighbor
            for nb in sorted(graph[current_city]):  # deterministic order
                options.append(("flight", nb))

        # For each option, apply presence (destination is also present on the same day if we fly), and recurse
        for mode, dest in options:
            # Prepare presence and counts for dest presence on this day (if flight)
            added_dest = False
            if mode == "flight" and dest is not None:
                # Mark destination presence on this day
                if dest not in presence_by_day[day]:
                    presence_by_day[day].add(dest)
                    counts[dest] += 1
                    added_dest = True
                # Additional check: after adding dest presence, ensure req_today (if any) is satisfied
                # (If we stayed and req_today requires another city not current, it's already excluded by forced_destination logic)
                # Also feasible check again (counts updated)
                if not feasible(counts, day):
                    if added_dest:
                        counts[dest] -= 1
                        presence_by_day[day].remove(dest)
                    continue

            # Next day's current city
            next_city = current_city if mode == "stay" else dest

            # Record move
            moves.append((day, current_city, None if mode == "stay" else dest))

            # Recurse to next day
            dfs(day + 1, next_city, counts, presence_by_day, moves, flights_used + (1 if mode == "flight" else 0))

            # Undo move
            moves.pop()
            if added_dest:
                counts[dest] -= 1
                presence_by_day[day].remove(dest)

        # Undo today's presence before returning
        if added_current:
            counts[current_city] -= 1
            presence_by_day[day].remove(current_city)

    # Initialize structures
    counts = {c: 0 for c in cities}
    presence_by_day = [set() for _ in range(total_days + 1)]  # 1-indexed by day
    moves = []

    # Run DFS
    dfs(1, start_city, counts, presence_by_day, moves, 0)

    # If no solution found (shouldn't happen), fallback to empty itinerary
    if best_solution["presence_by_day"] is None:
        return {"itinerary": []}

    # Build day-range segments per city from presence_by_day
    presence = best_solution["presence_by_day"]

    def build_segments_for_city(city):
        segments = []
        start = None
        for d in range(1, total_days + 1):
            if city in presence[d]:
                if start is None:
                    start = d
            else:
                if start is not None:
                    segments.append((start, d - 1))
                    start = None
        if start is not None:
            segments.append((start, total_days))
        return segments

    itinerary_list = []
    # To make output more readable, order segments chronologically across cities
    # Build all segment entries with (start_day, end_day, city) and then sort by start_day, then by end_day length descending
    all_segments = []
    for c in cities:
        segs = build_segments_for_city(c)
        for (s, e) in segs:
            all_segments.append((s, e, c))
    all_segments.sort(key=lambda x: (x[0], x[1], x[2]))

    for s, e, c in all_segments:
        itinerary_list.append({"day_range": f"Day {s}-{e}", "place": c})

    return {"itinerary": itinerary_list}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result))
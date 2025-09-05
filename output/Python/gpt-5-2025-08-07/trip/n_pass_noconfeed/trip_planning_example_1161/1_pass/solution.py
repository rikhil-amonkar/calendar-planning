import json
from collections import defaultdict

def build_adjacency():
    pairs = [
        ("Oslo", "Krakow", "and"),
        ("Oslo", "Paris", "and"),
        ("Paris", "Madrid", "and"),
        ("Helsinki", "Vilnius", "and"),
        ("Oslo", "Madrid", "and"),
        ("Oslo", "Helsinki", "and"),
        ("Helsinki", "Krakow", "and"),
        ("Dubrovnik", "Helsinki", "and"),
        ("Dubrovnik", "Madrid", "and"),
        ("Oslo", "Dubrovnik", "and"),
        ("Krakow", "Paris", "and"),
        ("Madrid", "Mykonos", "and"),
        ("Oslo", "Vilnius", "and"),
        ("Krakow", "Vilnius", "from"),
        ("Helsinki", "Paris", "and"),
        ("Vilnius", "Paris", "and"),
        ("Helsinki", "Madrid", "and"),
    ]
    adj = defaultdict(set)
    for a, b, t in pairs:
        if t == "and":
            adj[a].add(b)
            adj[b].add(a)
        elif t == "from":
            adj[a].add(b)
    return adj

def compress_segments(presence_by_day, cities):
    # presence_by_day: dict day -> set(cities present)
    # For each city, gather contiguous day ranges
    segments = []
    for city in cities:
        days = sorted([d for d in presence_by_day if city in presence_by_day[d]])
        if not days:
            continue
        start = days[0]
        prev = days[0]
        for d in days[1:]:
            if d == prev + 1:
                prev = d
            else:
                segments.append({"day_range": f"Day {start}-{prev}", "place": city})
                start = d
                prev = d
        segments.append({"day_range": f"Day {start}-{prev}", "place": city})
    # Sort by starting day numeric
    def start_day(seg):
        s = seg["day_range"].split()[1]
        a, b = s.split("-")
        return int(a)
    segments.sort(key=start_day)
    return segments

def solve_itinerary():
    total_days = 18
    cities = ["Oslo", "Krakow", "Paris", "Madrid", "Helsinki", "Vilnius", "Dubrovnik", "Mykonos"]

    # Required total presence days per city
    required_days = {
        "Mykonos": 4,
        "Krakow": 5,
        "Vilnius": 2,
        "Helsinki": 2,
        "Dubrovnik": 3,
        "Oslo": 2,
        "Madrid": 5,
        "Paris": 2,
    }

    # Daily required presence constraints
    daily_required = {d: set() for d in range(1, total_days + 1)}
    daily_required[1].add("Oslo")
    daily_required[2].update(["Oslo", "Dubrovnik"])
    daily_required[3].add("Dubrovnik")
    daily_required[4].add("Dubrovnik")
    for d in range(15, 19):
        daily_required[d].add("Mykonos")

    # Additional allowed windows (to reduce search)
    allowed_windows = {
        "Dubrovnik": (2, 4),
        "Mykonos": (15, 18),
    }

    adj = build_adjacency()

    # Pre-check: ensure graph contains all cities
    for c in cities:
        if c not in adj:
            adj[c] = set()

    # DFS/backtracking
    best_plan = []
    presence_counts_init = {c: 0 for c in cities}
    presence_by_day_init = {d: set() for d in range(1, total_days + 1)}

    def can_include_city_on_day(city, day, counts):
        # Respect allowed window if defined
        if city in allowed_windows:
            start, end = allowed_windows[city]
            if not (start <= day <= end):
                return False
        # Respect total required days cap
        if counts[city] + 1 > required_days[city]:
            return False
        return True

    def remaining_feasible(day, counts):
        # Basic feasibility: for each city, remaining days needed must fit
        # into remaining calendar days, allowing at most one overlap per day via flights.
        # The absolute maximum city-presences left from day..end is:
        # remaining_days + maximum_flights_possible. Maximum flights cannot exceed remaining_days
        # but tight bound is complex; we do a simple necessary condition:
        rem_days = total_days - day + 1
        remaining_needed_total = sum(required_days[c] - counts[c] for c in cities)
        # Max extra city-days beyond rem_days is at most rem_days (if flying every remaining day),
        # giving an upper bound of 2*rem_days city-presences left. Necessary condition:
        return remaining_needed_total <= 2 * rem_days

    def dfs(day, current_city, counts, presence_by_day, plan):
        nonlocal best_plan
        if day > total_days:
            # Check all counts match requirements exactly
            for c in cities:
                if counts[c] != required_days[c]:
                    return False
            best_plan = plan[:]
            return True

        # Fast fail: if remaining needed cannot fit in remaining days
        if not remaining_feasible(day, counts):
            return False

        req = daily_required[day]

        # Helper to try an option (stay or fly)
        def try_option(stay, dest=None):
            # Build presence set for the day
            if stay:
                presence = {current_city}
                end_city = current_city
            else:
                if dest is None:
                    return False
                # Only one flight per day
                presence = {current_city, dest}
                end_city = dest

            # Must include required daily cities
            if not req.issubset(presence):
                return False

            # Check city inclusion constraints for this day
            # Each city in presence must be allowed on this day and not exceed counts
            for c in presence:
                if not can_include_city_on_day(c, day, counts):
                    return False

            # Heuristic: if both today and tomorrow require the current city, we avoid leaving it today
            if day < total_days:
                tomorrow_req = daily_required[day + 1]
                if {current_city} == tomorrow_req and current_city in req:
                    # today requires current_city and tomorrow requires current_city
                    # Do not leave current_city today
                    if not stay:
                        return False

            # Apply this day's presence
            for c in presence:
                counts[c] += 1
            presence_by_day[day] = presence
            if stay:
                plan.append({"day": day, "action": "stay", "from": current_city, "to": current_city, "cities": sorted(list(presence))})
            else:
                plan.append({"day": day, "action": "fly", "from": current_city, "to": dest, "cities": sorted(list(presence))})

            # Recurse
            ok = dfs(day + 1, end_city, counts, presence_by_day, plan)
            if ok:
                return True

            # Backtrack
            plan.pop()
            presence_by_day[day] = set()
            for c in presence:
                counts[c] -= 1
            return False

        # Generate options based on requirements and adjacency
        options_tried = 0

        # If requirement has two cities, must be flight from current_city to the other
        if len(req) == 2:
            if current_city in req:
                dest = (req - {current_city}).pop()
                if dest in adj[current_city]:
                    if try_option(False, dest):
                        return True
                    options_tried += 1
            # No other possibility
            return False

        # If requirement has one city
        if len(req) == 1:
            r = next(iter(req))
            if r == current_city:
                # Can stay
                if try_option(True):
                    return True
                options_tried += 1
                # Or fly to neighbor
                for y in sorted(adj[current_city]):
                    # Presence {current_city, y}
                    if try_option(False, y):
                        return True
                    options_tried += 1
            else:
                # Must include r; with one flight, must fly to r if possible
                if r in adj[current_city]:
                    if try_option(False, r):
                        return True
                    options_tried += 1
                else:
                    return False
        else:
            # No specific daily requirement: choose to stay or fly
            # Stay option
            if try_option(True):
                return True
            options_tried += 1
            # Fly options
            for y in sorted(adj[current_city]):
                if try_option(False, y):
                    return True
                options_tried += 1

        return False

    # Initialize and run DFS
    start_city = "Oslo"
    counts = presence_counts_init.copy()
    presence_by_day = {d: set() for d in presence_by_day_init}
    plan = []

    # Day 1 must include Oslo; start in Oslo and choose "stay" or "fly" via DFS
    dfs(1, start_city, counts, presence_by_day, plan)

    # Build itinerary segments from presence_by_day
    segments = compress_segments(presence_by_day, cities)
    return {"itinerary": segments}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False))
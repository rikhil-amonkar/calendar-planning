import json
from collections import defaultdict

def compute_itinerary():
    # Input variables based on constraints
    cities = ["Prague", "Lyon", "Frankfurt", "Helsinki", "Naples"]
    adjacency = {
        "Prague": {"Lyon", "Frankfurt", "Helsinki"},
        "Lyon": {"Prague", "Frankfurt"},
        "Frankfurt": {"Lyon", "Prague", "Helsinki", "Naples"},
        "Helsinki": {"Naples", "Frankfurt", "Prague"},
        "Naples": {"Helsinki", "Frankfurt"},
    }
    total_days = 12
    required_city_days = {
        "Prague": 2,
        "Lyon": 3,
        "Frankfurt": 3,
        "Helsinki": 4,
        "Naples": 4,
    }
    # Event/day inclusion constraints:
    # - Must be in Prague on day 1 and day 2 (workshop between day 1 and day 2)
    # - Must be in Helsinki on days 2-5 (annual show)
    # Also, exactly the required counts for each city (no extra days)
    required_inclusions_by_day = {
        1: {"Prague"},
        2: {"Prague", "Helsinki"},
        3: {"Helsinki"},
        4: {"Helsinki"},
        5: {"Helsinki"},
    }
    # Allowed days (to keep exact targets for Prague and Helsinki)
    allowed_days_by_city = {
        "Prague": {1, 2},
        "Helsinki": {2, 3, 4, 5},
        # Others unrestricted; exact counts will constrain them
    }
    # Derived: number of flight days needed to make up for overlapping days
    total_presence_required = sum(required_city_days.values())
    required_flights = total_presence_required - total_days  # Each flight day contributes an extra presence
    
    # Backtracking state
    presence_by_day = [set() for _ in range(total_days + 1)]  # 1-indexed
    actions_by_day = [None for _ in range(total_days + 1)]    # store dicts: {'action': 'stay'|'fly', 'from': c, 'to': c2|None}
    counts_init = {c: 0 for c in cities}

    # Helper: feasibility check for future requirements
    def future_requirements_feasible(day, counts_now):
        # Ensure that for each future required inclusion day, the city still has remaining quota
        rem_counts = {c: required_city_days[c] - counts_now[c] for c in cities}
        for d in range(day + 1, total_days + 1):
            for c in required_inclusions_by_day.get(d, set()):
                if rem_counts.get(c, 0) <= 0:
                    return False
                rem_counts[c] -= 1
        # Ensure allowed windows for cities are sufficient for remaining allocations
        for c, allowed_set in allowed_days_by_city.items():
            remaining_allowed_days = sum(1 for d in range(day + 1, total_days + 1) if d in allowed_set)
            if rem_counts[c] > remaining_allowed_days:
                return False
        return True

    def backtrack(day, current_city, counts, flights_used):
        # If finished all days, validate counts and flights
        if day > total_days:
            if counts == required_city_days and flights_used == required_flights:
                return True
            return False

        req_cities = required_inclusions_by_day.get(day, set())

        # Generate options: stay or fly to a neighbor
        options = []
        # Stay option
        options.append(("stay", current_city, current_city, {current_city}))
        # Fly options
        for nb in sorted(adjacency[current_city]):
            options.append(("fly", current_city, nb, {current_city, nb}))

        # Try options with pruning
        for action, src, dst, presence in options:
            # Must include required cities for this day
            if not req_cities.issubset(presence):
                continue
            # Allowed day windows for some cities (Helsinki, Prague)
            allowed_ok = True
            for c in presence:
                if c in allowed_days_by_city and day not in allowed_days_by_city[c]:
                    allowed_ok = False
                    break
            if not allowed_ok:
                continue

            # Update counts and check not exceeding required
            new_counts = counts.copy()
            for c in presence:
                new_counts[c] += 1
            if any(new_counts[c] > required_city_days[c] for c in cities):
                continue

            # Update flights used
            new_flights_used = flights_used + (1 if action == "fly" else 0)
            if new_flights_used > required_flights:
                continue

            # Bounds on flights feasibility
            remaining_days = total_days - day
            rem_presence_needed = sum(required_city_days[c] - new_counts[c] for c in cities)
            min_extra_flights_needed = max(0, rem_presence_needed - remaining_days)
            if new_flights_used + min_extra_flights_needed > required_flights:
                continue
            if new_flights_used + remaining_days < required_flights:
                continue

            # Future inclusion feasibility
            if not future_requirements_feasible(day, new_counts):
                continue

            # Commit for this day
            presence_by_day[day] = presence
            actions_by_day[day] = {
                "action": action,
                "from": src,
                "to": (dst if action == "fly" else None),
            }

            next_city = dst if action == "fly" else current_city
            if backtrack(day + 1, next_city, new_counts, new_flights_used):
                return True

            # Backtrack implicit by loop

        return False

    # Start in Prague (must be in Prague on Day 1)
    start_city = "Prague"
    solved = backtrack(1, start_city, counts_init, 0)
    if not solved:
        # If, for some reason, no solution found, return empty itinerary
        return {"itinerary": []}

    # Aggregate presence into day ranges per city (overlapping ranges allowed for flight days)
    segments = []
    for city in cities:
        start = None
        prev = None
        for d in range(1, total_days + 1):
            if city in presence_by_day[d]:
                if start is None:
                    start = d
                prev = d
            else:
                if start is not None:
                    segments.append({"day_range": f"Day {start}-{prev}", "place": city})
                    start = None
                    prev = None
        if start is not None:
            segments.append({"day_range": f"Day {start}-{prev}", "place": city})

    # Sort segments by starting day for readability
    def seg_key(seg):
        # Extract first day number from "Day X-Y"
        part = seg["day_range"].split()[1]
        start_day = int(part.split("-")[0])
        return start_day, cities.index(seg["place"])

    segments.sort(key=seg_key)

    return {"itinerary": segments}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))
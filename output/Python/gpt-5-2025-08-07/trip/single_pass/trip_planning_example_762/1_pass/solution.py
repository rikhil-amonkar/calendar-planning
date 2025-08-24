import json
import itertools

def find_itinerary():
    # Input variables (constraints)
    total_days = 13
    cities_with_durations = {
        "Dublin": 3,
        "Madrid": 2,
        "Oslo": 3,
        "London": 2,
        "Vilnius": 3,
        "Berlin": 5,
    }
    # Time-window constraints: must be in city on at least one day within [start_day, end_day] inclusive
    window_constraints = [
        {"city": "Dublin", "start_day": 7, "end_day": 9},   # meet friends
        {"city": "Madrid", "start_day": 2, "end_day": 3},   # visit relatives
        {"city": "Berlin", "start_day": 3, "end_day": 7},   # attend wedding
    ]
    # Direct flight connections (undirected)
    direct_flights = {
        frozenset(("London", "Madrid")),
        frozenset(("Oslo", "Vilnius")),
        frozenset(("Berlin", "Vilnius")),
        frozenset(("Madrid", "Oslo")),
        frozenset(("Madrid", "Dublin")),
        frozenset(("London", "Oslo")),
        frozenset(("Madrid", "Berlin")),
        frozenset(("Berlin", "Oslo")),
        frozenset(("Dublin", "Oslo")),
        frozenset(("London", "Dublin")),
        frozenset(("London", "Berlin")),
        frozenset(("Berlin", "Dublin")),
    }

    cities = list(cities_with_durations.keys())
    required_extra_counts = sum(cities_with_durations.values()) - total_days
    # With one flight per day, total counts = total_days + number_of_flights
    # For a chain visiting each city exactly once, flights = len(cities) - 1
    if required_extra_counts != len(cities) - 1:
        raise ValueError("Durations vs total_days mismatch for a single-visit chain with one flight per transition.")

    def has_direct_flight(a, b):
        return frozenset((a, b)) in direct_flights

    def build_schedule(order):
        # Build overlapping day ranges per city:
        # Segment k starts at start_k and ends at end_k = start_k + duration_k - 1
        # Next segment starts at same day as previous end (flight day counts for both)
        schedule = {}
        start_day = 1
        for idx, city in enumerate(order):
            dur = cities_with_durations[city]
            end_day = start_day + dur - 1
            schedule[city] = (start_day, end_day)
            # Validate direct flight to next (if exists)
            if idx < len(order) - 1:
                next_city = order[idx + 1]
                if not has_direct_flight(city, next_city):
                    return None  # invalid due to missing direct flight
                # Next start is overlapping on this end_day (flight day)
                start_day = end_day
        # After last city
        final_end = end_day
        if final_end != total_days:
            return None  # does not span correct total days
        return schedule

    def satisfies_windows(schedule):
        for wc in window_constraints:
            city = wc["city"]
            w_s, w_e = wc["start_day"], wc["end_day"]
            c_s, c_e = schedule[city]
            # Intersection check
            if c_e < w_s or c_s > w_e:
                return False
        return True

    # Optimization objective:
    # 1) Feasible schedules only.
    # 2) Minimize a tie-breaker score: sum over windows of distance of window midpoint to nearest covered day (0 if intersects).
    # 3) If still tied, lexicographically smallest order tuple.
    best = None  # (score, order_tuple, schedule_dict)

    for order in itertools.permutations(cities):
        # adjacency check is inside build_schedule
        schedule = build_schedule(order)
        if schedule is None:
            continue
        if not satisfies_windows(schedule):
            continue

        # Compute tie-breaker score (should be 0 for all feasible because of intersection, but keep generic)
        score = 0
        for wc in window_constraints:
            city = wc["city"]
            w_s, w_e = wc["start_day"], wc["end_day"]
            mid = (w_s + w_e) / 2.0
            c_s, c_e = schedule[city]
            if c_e < w_s:
                dist = w_s - c_e
            elif c_s > w_e:
                dist = c_s - w_e
            else:
                dist = 0
            score += dist * dist

        candidate = (score, order, schedule)
        if best is None or candidate[0] < best[0] or (candidate[0] == best[0] and candidate[1] < best[1]):
            best = candidate

    if best is None:
        raise RuntimeError("No feasible itinerary found under given constraints.")

    _, best_order, best_schedule = best

    # Build output itinerary as a list of day_range blocks, ordered chronologically by start day
    itinerary_list = []
    # Sort by segment start day according to best_order sequence
    for city in best_order:
        s, e = best_schedule[city]
        itinerary_list.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    return {"itinerary": itinerary_list}

if __name__ == "__main__":
    result = find_itinerary()
    print(json.dumps(result))
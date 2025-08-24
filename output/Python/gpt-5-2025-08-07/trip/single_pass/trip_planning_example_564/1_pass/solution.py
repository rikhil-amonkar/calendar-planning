import itertools
import json

def compute_itinerary():
    # Input variables (trip constraints)
    total_days = 16
    cities = ["Rome", "Seville", "Istanbul", "Naples", "Santorini"]
    durations = {
        "Istanbul": 2,
        "Rome": 3,
        "Seville": 4,
        "Naples": 7,
        "Santorini": 4
    }
    # Direct flight edges (undirected)
    direct_flights = {
        frozenset(("Rome", "Santorini")),
        frozenset(("Seville", "Rome")),
        frozenset(("Istanbul", "Naples")),
        frozenset(("Naples", "Santorini")),
        frozenset(("Rome", "Naples")),
        frozenset(("Rome", "Istanbul")),
    }
    # Anchors: presence requirements
    anchors = {
        "Istanbul": {"must_cover_days": set([6, 7])},           # visit relatives days 6-7; duration 2 => exactly these days
        "Santorini": {"must_cover_days": set([13, 14, 15, 16])} # wedding days 13-16; duration 4 => exactly these days
    }

    # Helper to validate adjacency path (only direct flights between consecutive cities)
    def is_valid_path(order):
        for a, b in zip(order, order[1:]):
            if frozenset((a, b)) not in direct_flights:
                return False
        return True

    # Compute schedule for a given order using overlaps on flight days
    def compute_schedule(order):
        schedule = {}
        # Start first city on Day 1
        start_day = 1
        for i, city in enumerate(order):
            if i == 0:
                s = start_day
            else:
                # flight day overlaps: start of current = end of previous
                prev_city = order[i - 1]
                s = schedule[prev_city]["end"]
            e = s + durations[city] - 1
            schedule[city] = {"start": s, "end": e}
        return schedule

    # Validate anchors precisely (since anchor day counts match the required duration)
    def anchors_satisfied(schedule):
        for city, rule in anchors.items():
            must = rule["must_cover_days"]
            s = schedule[city]["start"]
            e = schedule[city]["end"]
            city_days = set(range(s, e + 1))
            if must != city_days:
                return False
        return True

    # Search for a feasible and "optimal" (constraint-satisfying) itinerary
    best_itinerary = None
    for order in itertools.permutations(cities, len(cities)):
        # Must cover all cities once
        if set(order) != set(cities):
            continue
        # Path must respect direct flights between consecutive cities
        if not is_valid_path(order):
            continue
        # Compute schedule based on durations and overlaps
        schedule = compute_schedule(order)

        # The overall trip must exactly span Day 1 to Day total_days (end of last city)
        last_city = order[-1]
        if schedule[last_city]["end"] != total_days:
            continue
        if schedule[order[0]]["start"] != 1:
            continue

        # Check anchors (Istanbul days 6-7 and Santorini days 13-16)
        if not anchors_satisfied(schedule):
            continue

        # If we reach here, we have a valid itinerary; select the first found as optimal
        itinerary = []
        for city in order:
            s = schedule[city]["start"]
            e = schedule[city]["end"]
            itinerary.append({
                "day_range": f"Day {s}-{e}",
                "place": city
            })
        best_itinerary = itinerary
        break

    if best_itinerary is None:
        raise RuntimeError("No feasible itinerary found with the given constraints.")

    return {"itinerary": best_itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result))
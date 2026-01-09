import json
from constraint import Problem

def main():
    # Input variables (trip constraints)
    total_days = 13
    cities = ["Seville", "Stuttgart", "Porto", "Madrid"]

    required_city_days = {
        "Seville": 2,
        "Stuttgart": 7,
        "Porto": 3,
        "Madrid": 4,
    }

    # Direct flights (undirected edges)
    direct_flights = {
        frozenset(["Porto", "Stuttgart"]),
        frozenset(["Seville", "Porto"]),
        frozenset(["Madrid", "Porto"]),
        frozenset(["Madrid", "Seville"]),
    }

    # Special constraints
    must_be_in_stuttgart_days = [7, 13]
    # Must visit relatives in Madrid between day 1 and day 4 (at least one day within this window)
    madrid_visit_window = range(1, 5)

    # Build CSP
    problem = Problem()
    # Variables: start city for day 0 (the city you wake up in on day 1),
    # and end_city[d] = city at the end of day d (after any travel that day).
    problem.addVariable("start", cities)
    for d in range(1, total_days + 1):
        problem.addVariable(f"end_{d}", cities)

    # Step constraints: If end city changes on day d, it must be a direct flight
    def step_constraint(prev, curr):
        if prev == curr:
            return True
        return frozenset([prev, curr]) in direct_flights

    # Link day 1 to start
    problem.addConstraint(step_constraint, ["start", "end_1"])
    # Link all subsequent days to previous day's end
    for d in range(2, total_days + 1):
        problem.addConstraint(step_constraint, [f"end_{d-1}", f"end_{d}"])

    # Global constraint to enforce:
    # - exact city-day counts considering travel days count for both cities
    # - presence in Stuttgart on specific days
    # - at least one day in Madrid in days 1..4
    def global_counts_constraint(*vars_tuple):
        # vars order: start, end_1, end_2, ..., end_13
        start = vars_tuple[0]
        ends = list(vars_tuple[1:])

        # Count presence days per city
        counts = {c: 0 for c in cities}

        def present_on_day(d, city):
            # d = 1..total_days (1-indexed)
            prev = start if d == 1 else ends[d - 2]
            curr = ends[d - 1]
            if prev == curr:
                return prev == city
            else:
                return prev == city or curr == city

        # Tally counts and check presence constraints
        for d in range(1, total_days + 1):
            prev = start if d == 1 else ends[d - 2]
            curr = ends[d - 1]
            if prev == curr:
                counts[prev] += 1
            else:
                counts[prev] += 1
                counts[curr] += 1

        # Check exact counts
        for c, req in required_city_days.items():
            if counts[c] != req:
                return False

        # Must be present in Stuttgart on specific days
        for d in must_be_in_stuttgart_days:
            if not present_on_day(d, "Stuttgart"):
                return False

        # Must visit relatives in Madrid on at least one day in the window 1..4
        if not any(present_on_day(d, "Madrid") for d in madrid_visit_window):
            return False

        return True

    problem.addConstraint(global_counts_constraint, ["start"] + [f"end_{d}" for d in range(1, total_days + 1)])

    solution = problem.getSolution()

    itinerary = []
    if solution is None:
        # No solution found; return empty itinerary
        output = {"itinerary": itinerary}
        print(json.dumps(output))
        return

    # Construct human-friendly per-day itinerary, noting travel days
    per_day = []
    start_city = solution["start"]
    prev = start_city
    for d in range(1, total_days + 1):
        curr = solution[f"end_{d}"]
        if prev == curr:
            place_str = curr
        else:
            place_str = f"Travel: {prev} to {curr} (both cities)"
        per_day.append((d, place_str))
        prev = curr

    # Compress consecutive days with the same "place" into day ranges
    def flush_segment(seg_start_day, seg_end_day, place):
        if seg_start_day == seg_end_day:
            day_range = f"Day {seg_start_day}"
        else:
            day_range = f"Day {seg_start_day}-{seg_end_day}"
        itinerary.append({"day_range": day_range, "place": place})

    if per_day:
        seg_start = per_day[0][0]
        seg_place = per_day[0][1]
        last_day = per_day[0][0]
        for (day, place) in per_day[1:]:
            if place == seg_place and day == last_day + 1:
                last_day = day
            else:
                flush_segment(seg_start, last_day, seg_place)
                seg_start = day
                seg_place = place
                last_day = day
        flush_segment(seg_start, last_day, seg_place)

    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()
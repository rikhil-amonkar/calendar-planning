import json
import itertools

def main():
    total_days = 26

    # Required stay lengths per city
    durations = {
        "Prague": 3,
        "Warsaw": 4,
        "Dublin": 3,
        "Athens": 3,
        "Vilnius": 4,
        "Porto": 5,
        "London": 3,
        "Seville": 2,
        "Lisbon": 5,
        "Dubrovnik": 3,
    }

    # Fixed presence windows (inclusive)
    windows = {
        "Prague": (1, 3),
        "London": (3, 5),
        "Lisbon": (5, 9),
        "Porto": (16, 20),
        "Warsaw": (20, 23),
    }

    # Direct flights (undirected)
    direct_pairs = [
        ("Warsaw", "Vilnius"),
        ("Prague", "Athens"),
        ("London", "Lisbon"),
        ("Lisbon", "Porto"),
        ("Prague", "Lisbon"),
        ("London", "Dublin"),
        ("Athens", "Vilnius"),
        ("Athens", "Dublin"),
        ("Prague", "London"),
        ("London", "Warsaw"),
        ("Dublin", "Seville"),
        ("Seville", "Porto"),
        ("Lisbon", "Athens"),
        ("Dublin", "Porto"),
        ("Athens", "Warsaw"),
        ("Lisbon", "Warsaw"),
        ("Porto", "Warsaw"),
        ("Prague", "Warsaw"),
        ("Prague", "Dublin"),
        ("Athens", "Dubrovnik"),
        ("Lisbon", "Dublin"),
        ("Dubrovnik", "Dublin"),
        ("Lisbon", "Seville"),
        ("London", "Athens"),
    ]

    # Build adjacency
    adj = {}
    cities = set(durations.keys())
    for a, b in direct_pairs:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)

    def has_direct(a, b):
        return b in adj.get(a, set())

    # Initialize day presence map
    day_presence = {d: set() for d in range(1, total_days + 1)}
    flights = []  # (day, from, to)

    def occupy_range(city, start, end):
        for d in range(start, end + 1):
            if 1 <= d <= total_days:
                day_presence[d].add(city)

    def fly(day, from_city, to_city):
        if not has_direct(from_city, to_city):
            raise ValueError(f"No direct flight from {from_city} to {to_city} on day {day}")
        if not (1 <= day <= total_days):
            raise ValueError(f"Flight day {day} out of range")
        day_presence[day].add(from_city)
        day_presence[day].add(to_city)
        flights.append((day, from_city, to_city))

    # 1) Occupy fixed windows
    for city, (s, e) in windows.items():
        occupy_range(city, s, e)

    # 2) Schedule direct flights at exact window boundaries where possible and needed
    # Sort windows by start day to establish order
    ordered_windows = sorted(windows.items(), key=lambda kv: kv[1][0])  # (city, (start,end))

    for i in range(len(ordered_windows) - 1):
        city_a, (start_a, end_a) = ordered_windows[i]
        city_b, (start_b, end_b) = ordered_windows[i + 1]
        # If the next window starts exactly when the previous ends, we move the same day
        if end_a == start_b:
            # Fly on the end_a day from city_a to city_b
            fly(end_a, city_a, city_b)

    # 3) Fill the gap between Lisbon (ends day 9) and Porto (starts day 16)
    gap_start_city = "Lisbon"
    gap_end_city = "Porto"
    gap_start_day = windows[gap_start_city][1]  # 9
    gap_end_day = windows[gap_end_city][0]      # 16

    # Remaining cities to visit in the gap (except fixed-window cities and Vilnius which will be post-Warsaw)
    fixed_cities = set(windows.keys())
    gap_cities = [c for c in cities if c not in fixed_cities and c != "Vilnius"]  # Dublin, Athens, Seville, Dubrovnik
    # Ensure correct set
    assert set(gap_cities) == {"Dublin", "Athens", "Seville", "Dubrovnik"}

    # We need a path order that connects gap_start_city -> C1 -> C2 -> C3 -> C4 -> gap_end_city via direct flights
    # and fits within the calendar: entry on day gap_start_day and final flight to gap_end_city on day gap_end_day.
    # The span formula: gap_start_day + sum(ri) - k == gap_end_day where ri are durations and k is number of gap cities
    k = len(gap_cities)
    target_span_ok = (gap_start_day + sum(durations[c] for c in gap_cities) - k) == gap_end_day

    if not target_span_ok:
        raise ValueError("Gap durations do not align with available days")

    gap_order = None
    for perm in itertools.permutations(gap_cities):
        ok = True
        # connectivity check across chain
        if not has_direct(gap_start_city, perm[0]):
            ok = False
        if ok:
            for i in range(len(perm) - 1):
                if not has_direct(perm[i], perm[i + 1]):
                    ok = False
                    break
        if ok and not has_direct(perm[-1], gap_end_city):
            ok = False
        if ok:
            gap_order = list(perm)
            break

    if gap_order is None:
        raise ValueError("No valid gap path found with direct flights")

    # Simulate the gap scheduling using the overlap-on-flight-day rule
    current_day = gap_start_day  # day 9
    prev_city = gap_start_city
    # For each city in order, schedule arrival flight on current_day, interior days, and pass to next.
    for idx, city in enumerate(gap_order):
        # Flight from prev_city to city on current_day
        fly(current_day, prev_city, city)
        # City must have durations[city] total days; first counted today.
        next_flight_day = current_day + (durations[city] - 1)
        # Fill interior days (between arrival and next flight day)
        for d in range(current_day + 1, next_flight_day):
            day_presence[d].add(city)
        # Move forward
        prev_city = city
        current_day = next_flight_day

    # Final flight from last gap city to Porto on gap_end_day
    # current_day should equal gap_end_day (by construction)
    if current_day != gap_end_day:
        raise ValueError("Gap scheduling did not align to end day")
    fly(current_day, gap_order[-1], gap_end_city)

    # 4) Flight from Porto to Warsaw at the shared boundary day 20 (if not already scheduled by boundary logic)
    # The boundary scheduling above should already have added this flight if windows align.
    # Ensure it's present; if not, add it.
    if not any(d == windows["Porto"][1] and a == "Porto" and b == "Warsaw" or d == windows["Porto"][1] and a == "Warsaw" and b == "Porto" for d, a, b in flights):
        fly(windows["Porto"][1], "Porto", "Warsaw")

    # 5) After Warsaw window, schedule Vilnius for 4 days by flying on day 23
    # Warsaw window is 20-23; fly on day 23 to Vilnius
    fly(windows["Warsaw"][1], "Warsaw", "Vilnius")
    # Fill remaining Vilnius days 24-26
    for d in range(windows["Warsaw"][1] + 1, total_days + 1):
        day_presence[d].add("Vilnius")

    # Validation: Check each city meets its required duration and windows are satisfied
    city_days = {c: sorted([d for d in range(1, total_days + 1) if c in day_presence[d]]) for c in durations.keys()}

    # Check durations
    for c, req in durations.items():
        if len(city_days[c]) != req:
            raise AssertionError(f"City {c} has {len(city_days[c])} days, expected {req}")

    # Check windows coverage
    for c, (s, e) in windows.items():
        for d in range(s, e + 1):
            if c not in day_presence[d]:
                raise AssertionError(f"Window violation: {c} not present on day {d}")

    # Ensure each day has at least one city
    for d in range(1, total_days + 1):
        if not day_presence[d]:
            raise AssertionError(f"No city scheduled on day {d}")

    # Construct itinerary as contiguous ranges per city (min..max because schedules are contiguous)
    segments = []
    for c in durations.keys():
        days = city_days[c]
        start = min(days)
        end = max(days)
        segments.append((start, end, c))

    # Sort by start day
    segments.sort(key=lambda x: x[0])

    itinerary = []
    for start, end, place in segments:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": place
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
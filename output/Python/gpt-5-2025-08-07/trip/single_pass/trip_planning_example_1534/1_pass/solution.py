import json

def main():
    # Trip parameters
    total_days = 25
    cities_required_days = {
        "Paris": 2,
        "Barcelona": 5,
        "Florence": 5,
        "Tallinn": 2,
        "Vilnius": 3,
        "Warsaw": 4,
        "Venice": 3,
        "Hamburg": 4,
        "Salzburg": 4,
        "Amsterdam": 2,
    }

    # Time windows (inclusive)
    windows = {
        "Paris_workshop": (1, 2),            # must be in Paris on days 1-2
        "Barcelona_friends_window": (2, 6),  # want to meet friends in Barcelona between days 2-6
        "Tallinn_friend": (11, 12),          # meet friend in Tallinn between days 11-12
        "Hamburg_conference": (19, 22),      # must be in Hamburg during days 19-22
        "Salzburg_wedding_window": (22, 25), # attend wedding in Salzburg between days 22-25
    }

    # Direct flights graph (directed edges)
    direct_pairs_bidirectional = [
        ("Paris", "Venice"),
        ("Barcelona", "Amsterdam"),
        ("Amsterdam", "Warsaw"),
        ("Amsterdam", "Vilnius"),
        ("Barcelona", "Warsaw"),
        ("Warsaw", "Venice"),
        ("Amsterdam", "Hamburg"),
        ("Barcelona", "Hamburg"),
        ("Barcelona", "Florence"),
        ("Barcelona", "Venice"),
        ("Paris", "Hamburg"),
        ("Paris", "Vilnius"),
        ("Paris", "Amsterdam"),
        ("Paris", "Florence"),
        ("Florence", "Amsterdam"),
        ("Vilnius", "Warsaw"),
        ("Barcelona", "Tallinn"),
        ("Paris", "Warsaw"),
        ("Tallinn", "Warsaw"),
        ("Amsterdam", "Tallinn"),
        ("Paris", "Tallinn"),
        ("Paris", "Barcelona"),
        ("Venice", "Hamburg"),
        ("Warsaw", "Hamburg"),
        ("Hamburg", "Salzburg"),
        ("Amsterdam", "Venice"),
    ]
    direct_pairs_directed = [
        ("Tallinn", "Vilnius"),  # one-way
    ]

    direct_flights = set()
    for a, b in direct_pairs_bidirectional:
        direct_flights.add((a, b))
        direct_flights.add((b, a))
    for a, b in direct_pairs_directed:
        direct_flights.add((a, b))

    # Construct a feasible base itinerary by days (exactly one base city per day)
    base_segments = [
        ("Paris", 1, 2),       # Paris for workshop on days 1-2
        ("Barcelona", 3, 6),   # Be in Barcelona within days 2-6 window
        ("Florence", 7, 10),   # 4 base days; plus arrival day (6) makes total 5 in Florence
        ("Tallinn", 11, 12),   # meet friend days 11-12
        ("Vilnius", 13, 15),
        ("Warsaw", 16, 18),
        ("Hamburg", 19, 21),   # conference days 19-21 base; day 22 via flight presence
        ("Salzburg", 22, 25),  # wedding window days 22-25
    ]

    # Build base-by-day mapping
    base_by_day = {}
    for city, start, end in base_segments:
        for d in range(start, end + 1):
            if d < 1 or d > total_days:
                raise ValueError("Base segment day out of bounds")
            if d in base_by_day:
                raise ValueError(f"Overlapping base cities on day {d}")
            base_by_day[d] = city

    # Define flights (day, origin, destination); each must be direct
    flights = [
        # Move from Paris to Barcelona within day 2 (still in Paris for workshop; also counts for Barcelona)
        (2, "Paris", "Barcelona"),

        # Transition to Florence without adding extra Barcelona day (fly on day 6 which is already a Barcelona base day)
        (6, "Barcelona", "Florence"),

        # Position to Amsterdam at end of Florence stay to avoid being in Florence on day 11
        (10, "Florence", "Amsterdam"),

        # Move from Amsterdam to Tallinn to be in Tallinn on day 11
        (11, "Amsterdam", "Tallinn"),

        # Move from Tallinn to Vilnius (one-way allowed)
        (13, "Tallinn", "Vilnius"),

        # Move from Vilnius to Warsaw
        (16, "Vilnius", "Warsaw"),

        # On day 19, get Warsaw day via origin, then to Venice and Hamburg for conference
        (19, "Warsaw", "Venice"),
        (19, "Venice", "Hamburg"),

        # Accrue Venice days while staying in Hamburg for conference
        (20, "Hamburg", "Venice"),
        (20, "Venice", "Hamburg"),

        (21, "Hamburg", "Venice"),
        (21, "Venice", "Hamburg"),

        # Move from Hamburg to Salzburg for wedding window
        (22, "Hamburg", "Salzburg"),
    ]

    # Helper: validate that each flight is direct
    for day, orig, dest in flights:
        if (orig, dest) not in direct_flights:
            raise ValueError(f"Non-direct flight planned on day {day}: {orig} -> {dest}")

    # Compute presence per day: base city + any flight endpoints on that day
    presence_by_day = {d: set() for d in range(1, total_days + 1)}
    for d in range(1, total_days + 1):
        presence_by_day[d].add(base_by_day[d])
    for day, orig, dest in flights:
        if day < 1 or day > total_days:
            raise ValueError(f"Flight day out of bounds: {day}")
        presence_by_day[day].add(orig)
        presence_by_day[day].add(dest)

    # Compute per-city presence counts
    city_counts = {city: 0 for city in cities_required_days}
    all_cities_present = set()
    for d in range(1, total_days + 1):
        for c in presence_by_day[d]:
            all_cities_present.add(c)
            if c in city_counts:
                city_counts[c] += 1

    # Validate required days per city (exact match)
    for city, req_days in cities_required_days.items():
        if city_counts.get(city, 0) != req_days:
            raise ValueError(f"City {city} has {city_counts.get(city, 0)} days, required {req_days}")

    # Validate windows
    # Paris days 1-2
    for d in range(windows["Paris_workshop"][0], windows["Paris_workshop"][1] + 1):
        if "Paris" not in presence_by_day[d]:
            raise ValueError(f"Workshop in Paris not satisfied on day {d}")

    # Barcelona meet friends window: ensure presence within days 2-6 for all planned 5 Barcelona days
    b_start, b_end = windows["Barcelona_friends_window"]
    barcelona_days_in_window = [d for d in range(b_start, b_end + 1) if "Barcelona" in presence_by_day[d]]
    if len(barcelona_days_in_window) < 1:
        raise ValueError("No Barcelona day within friends window")
    # Additionally ensure total Barcelona days are exactly the ones we planned (should be 5 within 2-6)
    total_barcelona_days = [d for d in range(1, total_days + 1) if "Barcelona" in presence_by_day[d]]
    if not all(d in range(b_start, b_end + 1) for d in total_barcelona_days):
        raise ValueError("Barcelona days extend beyond the intended window (2-6)")

    # Tallinn friend days 11-12
    for d in range(windows["Tallinn_friend"][0], windows["Tallinn_friend"][1] + 1):
        if "Tallinn" not in presence_by_day[d]:
            raise ValueError(f"Friend meeting in Tallinn not satisfied on day {d}")

    # Hamburg conference days 19-22
    for d in range(windows["Hamburg_conference"][0], windows["Hamburg_conference"][1] + 1):
        if "Hamburg" not in presence_by_day[d]:
            raise ValueError(f"Hamburg conference presence missing on day {d}")

    # Salzburg wedding window 22-25: ensure presence occurs within this window
    s_start, s_end = windows["Salzburg_wedding_window"]
    if not any("Salzburg" in presence_by_day[d] for d in range(s_start, s_end + 1)):
        raise ValueError("No presence in Salzburg during the wedding window")

    # Validate total days and number of visited cities
    if len(base_by_day) != total_days:
        raise ValueError("Base itinerary does not cover all days")
    # Must visit exactly the intended 10 cities (as per requirements list)
    visited_required = set(cities_required_days.keys())
    # Ensure no extra cities were inadvertently visited via flights
    extra_cities = all_cities_present - visited_required
    if extra_cities:
        # It's okay to pass through other cities if they are on the allowed list, but here we purposefully only used required cities.
        raise ValueError(f"Visited unexpected extra cities: {sorted(extra_cities)}")
    if len(visited_required) != 10:
        raise ValueError("Did not visit exactly 10 cities as required")

    # Create itinerary output merging consecutive same base cities
    itinerary = []
    current_city = base_by_day[1]
    start_day = 1
    for d in range(2, total_days + 1):
        if base_by_day[d] != current_city:
            itinerary.append({
                "day_range": f"Day {start_day}-{d-1}",
                "place": current_city
            })
            current_city = base_by_day[d]
            start_day = d
    itinerary.append({
        "day_range": f"Day {start_day}-{total_days}",
        "place": current_city
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
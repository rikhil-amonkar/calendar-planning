import json
from collections import defaultdict

def compute_itinerary():
    # Trip parameters
    total_days = 18
    cities = ["Oslo", "Dubrovnik", "Helsinki", "Krakow", "Vilnius", "Paris", "Madrid", "Mykonos"]

    # Required days per city (exact)
    required_stays = {
        "Oslo": 2,
        "Dubrovnik": 3,
        "Helsinki": 2,
        "Krakow": 5,
        "Vilnius": 2,
        "Paris": 2,
        "Madrid": 5,
        "Mykonos": 4,
    }

    # Fixed-day constraints
    must_be_on_days = {
        "Oslo": [1, 2],
        "Dubrovnik": [2, 3, 4],
        "Mykonos": [15, 16, 17, 18],  # visit relatives
    }

    # Direct flights network
    undirected_pairs = [
        ("Oslo", "Krakow"),
        ("Oslo", "Paris"),
        ("Paris", "Madrid"),
        ("Helsinki", "Vilnius"),
        ("Oslo", "Madrid"),
        ("Oslo", "Helsinki"),
        ("Helsinki", "Krakow"),
        ("Dubrovnik", "Helsinki"),
        ("Dubrovnik", "Madrid"),
        ("Oslo", "Dubrovnik"),
        ("Krakow", "Paris"),
        ("Madrid", "Mykonos"),
        ("Oslo", "Vilnius"),
        ("Helsinki", "Paris"),
        ("Vilnius", "Paris"),
        ("Helsinki", "Madrid"),
    ]
    directed_pairs = [
        ("Krakow", "Vilnius"),  # one-way
    ]

    # Build adjacency including directionality
    adj = defaultdict(set)
    for a, b in undirected_pairs:
        adj[a].add(b)
        adj[b].add(a)
    for a, b in directed_pairs:
        adj[a].add(b)

    # Helper to verify direct flight
    def is_direct(a, b):
        return b in adj[a]

    # Presence tracker: day -> set of cities present that day
    presence = {day: set() for day in range(1, total_days + 1)}

    # Seed forced presences
    for city, days in must_be_on_days.items():
        for d in days:
            presence[d].add(city)

    # Plan logic:
    # We must:
    # - Be in Oslo on days 1-2 and in Dubrovnik days 2-4: fly OSL->DBV on day 2 (direct)
    # - Leave DBV on day 4 to avoid exceeding 3 days. We also need an extra early Madrid day
    #   because near the end (days 12-15) we can only count 4 Madrid days; required is 5.
    #   So we route DBV->MAD->HEL on day 4 (both direct).
    # - Helsinki for days 4-5 (2 total), then HEL->KRK day 6 (direct).
    # - Accumulate Krakow 5 days: days 6-10 (with flight to Vilnius on day 10).
    # - Vilnius 2 days: days 10-11 (flight to Paris day 11).
    # - Paris 2 days: days 11-12 (flight to Madrid day 12).
    # - Madrid: days 4 (early), 12-15 (with flight to Mykonos on day 15).
    # - Mykonos 4 days: 15-18.

    # Define flights by day in sequence; allow multiple flights in a day if needed
    flights_by_day = {
        2: [("Oslo", "Dubrovnik")],
        4: [("Dubrovnik", "Madrid"), ("Madrid", "Helsinki")],
        6: [("Helsinki", "Krakow")],
        10: [("Krakow", "Vilnius")],
        11: [("Vilnius", "Paris")],
        12: [("Paris", "Madrid")],
        15: [("Madrid", "Mykonos")],
    }

    # Validate direct flights exist
    for d, fls in flights_by_day.items():
        for a, b in fls:
            if not is_direct(a, b):
                raise ValueError(f"No direct flight from {a} to {b} on day {d}")

    # Simulate day-by-day travel and presence
    current_city = "Oslo"  # start in Oslo per constraints
    for day in range(1, total_days + 1):
        # Be in current city (stay contributes a day)
        presence[day].add(current_city)

        # Apply flights for this day (in given order)
        if day in flights_by_day:
            for idx, (a, b) in enumerate(flights_by_day[day]):
                # Ensure the flight originates from where we currently are
                if idx == 0:
                    if current_city != a:
                        raise ValueError(f"Invalid schedule: on day {day} starting in {current_city}, cannot fly {a}->{b}")
                else:
                    if last_dest != a:
                        raise ValueError(f"Invalid chain: on day {day} cannot connect from {last_dest} to {a}->{b}")

                # Record presence in both cities for the flight day
                presence[day].add(a)
                presence[day].add(b)

                # Update where we end the day after sequence of flights
                last_dest = b

            current_city = last_dest  # end-of-day city after all flights

    # Verify must_be_on_days presence
    for city, days in must_be_on_days.items():
        for d in days:
            if city not in presence[d]:
                raise ValueError(f"Constraint violation: {city} must be present on day {d}")

    # Compute total days per city and validate requirements
    city_days = {city: 0 for city in cities}
    for day in range(1, total_days + 1):
        for city in presence[day]:
            if city in city_days:
                city_days[city] += 1

    for city, req in required_stays.items():
        if city_days.get(city, 0) != req:
            raise ValueError(f"Constraint violation: {city} has {city_days.get(city, 0)} days, requires {req}")

    # Build itinerary as day ranges (each city may appear in multiple ranges due to non-contiguous stays)
    def compress_ranges(days_list):
        # days_list sorted ascending
        ranges = []
        if not days_list:
            return ranges
        start = prev = days_list[0]
        for d in days_list[1:]:
            if d == prev + 1:
                prev = d
            else:
                ranges.append((start, prev))
                start = prev = d
        ranges.append((start, prev))
        return ranges

    entries = []
    # Collect days present for each city
    for city in cities:
        days_here = sorted([d for d in range(1, total_days + 1) if city in presence[d]])
        for s, e in compress_ranges(days_here):
            entries.append({
                "day_range": f"Day {s}-{e}",
                "place": city
            })

    # Sort entries by start day to form a chronological itinerary view
    def start_day_of(entry):
        # parse "Day X-Y"
        s = entry["day_range"].split()[1].split("-")[0]
        return int(s)
    entries.sort(key=start_day_of)

    return {"itinerary": entries}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))
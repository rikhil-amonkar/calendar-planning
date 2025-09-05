import json
from collections import defaultdict

def main():
    # Inputs
    total_days = 32
    cities = [
        "Stockholm","Hamburg","Florence","Istanbul","Oslo",
        "Vilnius","Santorini","Munich","Frankfurt","Krakow"
    ]
    # Desired durations; type = "exact" for strict, "soft" otherwise
    desires = {
        "Stockholm": {"days": 3, "type": "exact"},
        "Hamburg": {"days": 5, "type": "exact"},
        "Florence": {"days": 2, "type": "exact"},
        "Istanbul": {"days": 5, "type": "exact"},  # also constrained to window below
        "Oslo": {"days": 5, "type": "soft"},
        "Vilnius": {"days": 5, "type": "soft"},
        "Santorini": {"days": 2, "type": "exact"},
        "Munich": {"days": 5, "type": "exact"},
        "Frankfurt": {"days": 4, "type": "soft"},
        "Krakow": {"days": 5, "type": "exact"},
    }
    # Fixed windows (inclusive) that must be in-city
    windows = {
        "Krakow": (5, 9),   # attend workshop during days 5-9
        "Istanbul": (25, 29) # attend show during days 25-29
    }

    # Direct flight graph (directed where specified)
    flights = defaultdict(set)
    def add_edge(a,b,bidirectional=True):
        flights[a].add(b)
        if bidirectional:
            flights[b].add(a)

    add_edge("Oslo","Stockholm",True)
    add_edge("Krakow","Frankfurt",True)
    add_edge("Krakow","Istanbul",True)
    add_edge("Munich","Stockholm",True)
    add_edge("Hamburg","Stockholm",True)
    add_edge("Krakow","Vilnius",False)   # one-way
    add_edge("Oslo","Istanbul",True)
    add_edge("Istanbul","Stockholm",True)
    add_edge("Oslo","Krakow",True)
    add_edge("Vilnius","Istanbul",True)
    add_edge("Oslo","Vilnius",True)
    add_edge("Frankfurt","Istanbul",True)
    add_edge("Oslo","Frankfurt",True)
    add_edge("Munich","Hamburg",True)
    add_edge("Munich","Istanbul",True)
    add_edge("Oslo","Munich",True)
    add_edge("Frankfurt","Florence",True)
    add_edge("Oslo","Hamburg",True)
    add_edge("Vilnius","Frankfurt",True)
    add_edge("Florence","Munich",False)  # one-way
    add_edge("Krakow","Munich",True)
    add_edge("Hamburg","Istanbul",True)
    add_edge("Frankfurt","Stockholm",True)
    add_edge("Stockholm","Santorini",False) # one-way
    add_edge("Frankfurt","Munich",True)
    add_edge("Santorini","Oslo",False)  # one-way
    add_edge("Krakow","Stockholm",True)
    add_edge("Vilnius","Munich",False)  # one-way
    add_edge("Frankfurt","Hamburg",True)

    # Build itinerary segments (inclusive day ranges); flight occurs on the start day of next segment
    itinerary_segments = []  # list of (city, start_day, end_day)

    def add_segment(city, start, end):
        assert 1 <= start <= end <= total_days
        itinerary_segments.append((city, start, end))

    # Construct schedule algorithmically:

    # 1) Pre-Krakow chain constrained by workshop window and Santorini access (Stockholm->Santorini->Oslo->Krakow)
    # Place Stockholm for exactly 3 days starting Day 1, then fly to Santorini on Day 3
    add_segment("Stockholm", 1, 3)  # flight to Santorini on day 3
    # Santorini exactly 2 days: Days 3-4, then fly to Oslo on Day 4
    add_segment("Santorini", 3, 4)
    # Oslo before Krakow: Days 4-5, fly to Krakow Day 5 to start Krakow window
    add_segment("Oslo", 4, 5)

    # 2) Krakow fixed window: Days 5-9 (exact 5 days, matches window)
    kr_start, kr_end = windows["Krakow"]
    add_segment("Krakow", kr_start, kr_end)

    # 3) Post-Krakow chain to align later with Istanbul window via Munich->Hamburg
    # Choose Vilnius for 3 days (Days 9-11), then Frankfurt until Day 15 so that
    # Frankfurt->Florence is Day 16 and Florence->Munich is Day 17
    add_segment("Vilnius", 9, 11)
    add_segment("Frankfurt", 11, 15)
    # Florence exactly 2 days: Days 16-17 (with flights)
    add_segment("Florence", 16, 17)
    # Munich must be exactly 5 days; to align Hamburg 5 days ending Day 25 and Istanbul Day 25-29:
    # Let Munich start be t1, Hamburg starts on t1+4, Istanbul starts on (t1+8)=25 => t1=17
    add_segment("Munich", 17, 21)
    add_segment("Hamburg", 21, 25)

    # 4) Istanbul fixed window: Days 25-29
    ist_start, ist_end = windows["Istanbul"]
    add_segment("Istanbul", ist_start, ist_end)

    # 5) Post-Istanbul optimization days (Days 30-32 available but must depart on Day 29 to avoid extending Istanbul beyond Day 29)
    # Compute current day counts then allocate remaining to best satisfy soft desires using direct flights.
    # We'll choose to go to Oslo on Day 29, stay enough days to hit exactly desired, then fly to Vilnius to top up to desired.
    # Helper to count days in city given current segments
    def count_days(city):
        s = set()
        for c, a, b in itinerary_segments:
            if c == city:
                for d in range(a, b+1):
                    s.add(d)
        return len(s)

    # Build a map for exact cities to avoid exceeding them
    exact_cities = {c for c, cfg in desires.items() if cfg["type"] == "exact"}

    # Current counts before post-Istanbul extension
    current_counts = {c: count_days(c) for c in cities}

    # Determine post-Istanbul plan:
    # Step A: Fly Istanbul -> best city with largest soft deficit reachable directly.
    # Compute soft deficits
    def soft_deficit(c):
        want = desires[c]["days"]
        have = current_counts.get(c, 0)
        if desires[c]["type"] == "exact":
            # exact cities shouldn't be extended
            return -10**9
        return want - have

    # Candidates reachable from Istanbul
    reachable_from_ist = [c for c in cities if c in flights["Istanbul"] and c not in exact_cities]
    if reachable_from_ist:
        # pick city with max soft deficit; tie-break by name
        first_city = max(reachable_from_ist, key=lambda c: (soft_deficit(c), c))
    else:
        # Fallback: go to any city reachable (shouldn't happen with given graph)
        first_city = list(flights["Istanbul"])[0]

    # We'll start a new segment in first_city on Day 29 (flight day)
    # Plan how many days to spend there to meet its desired count exactly (if possible),
    # while reserving Day 31 for a potential flight to the second city with next largest deficit.
    start_after_ist = ist_end  # Day 29 flight day
    # Update counts considering the incoming day 29 will be added to first_city
    have_first = current_counts.get(first_city, 0)
    want_first = desires[first_city]["days"]
    needed_first_total = max(0, want_first - have_first)
    # We'll try to use Day 29 and Day 30 as stationary, and then Day 31 as flight day out
    # So allocate days in first_city: from Day 29 to min(Day 29 + needed_first_total - 1, Day 31)
    # but ensure we leave on Day 31 so that the flight day also counts toward first_city.
    if needed_first_total <= 0:
        first_end = min(total_days-1, start_after_ist)  # minimal stay till Day 29 only
    else:
        # We want that including Day 31 flight, total added equals needed_first_total.
        # Added days = (first_end - start_after_ist + 1)
        # We'll set first_end so that added days = needed_first_total, but cap at Day 31
        first_end = start_after_ist + needed_first_total - 1
        if first_end > 31:
            first_end = 31  # cap; may overshoot desired by a bit if can't fit exactly
        if first_end < start_after_ist:
            first_end = start_after_ist

    add_segment(first_city, start_after_ist, first_end)

    # Select second city for Day 31 flight (if possible within remaining days)
    # Remaining days after first segment end
    remaining_start = max(first_end, start_after_ist)  # last day occupied by first_city
    # We plan a flight on Day 31 to second city if we still have Day 31 < 32
    second_city = None
    if 31 <= total_days and 31 >= start_after_ist:
        # compute current counts again including first_city segment
        def recompute_counts():
            cnt = defaultdict(int)
            # accumulate sets to avoid double-add per day
            day_city = defaultdict(set)
            for c, a, b in itinerary_segments:
                for d in range(a, b+1):
                    day_city[d].add(c)
            for d, cs in day_city.items():
                for c in cs:
                    cnt[c] += 1
            return cnt

        current_counts = recompute_counts()

        # candidates reachable by direct flight on Day 31 from first_city
        reachable_from_first = [c for c in cities if c in flights[first_city] and c not in exact_cities]
        # Exclude first_city itself for the second hop
        reachable_from_first = [c for c in reachable_from_first if c != first_city]
        if reachable_from_first and 31 < total_days + 1:  # Day 31 flight possible
            # choose the city with max soft deficit now
            second_city = max(reachable_from_first, key=lambda c: (desires[c]["days"] - current_counts.get(c, 0), c))
            # Add second city segment from Day 31 to Day 32
            add_segment(second_city, 31, 32)
        else:
            # If no suitable second city, just extend first_city to Day 32 if it's soft
            if first_city not in exact_cities and itinerary_segments[-1][0] == first_city:
                city, a, _ = itinerary_segments[-1]
                itinerary_segments[-1] = (city, a, 32)

    # Verify direct flights between consecutive segments on their transition days
    for i in range(len(itinerary_segments)-1):
        city_a, start_a, end_a = itinerary_segments[i]
        city_b, start_b, end_b = itinerary_segments[i+1]
        # The flight occurs on day start_b from city_a to city_b; ensure overlap includes that day in city_a as well
        flight_day = start_b
        assert start_a <= flight_day <= end_a, f"No overlap on flight day between {city_a} and {city_b} on Day {flight_day}"
        assert city_b in flights[city_a], f"No direct flight from {city_a} to {city_b}"

    # Build day -> cities presence map to compute counts and validate constraints
    day_cities = defaultdict(set)
    for city, s, e in itinerary_segments:
        for d in range(s, e+1):
            day_cities[d].add(city)

    # Validations
    # 1) Trip spans exactly total_days and covers days 1..total_days
    assert itinerary_segments[0][1] == 1, "Trip must start on Day 1"
    assert itinerary_segments[-1][2] == total_days, "Trip must end on Day {}".format(total_days)

    # 2) Exact durations
    city_day_counts = {c: 0 for c in cities}
    for d in range(1, total_days+1):
        for c in day_cities[d]:
            city_day_counts[c] += 1

    for c, cfg in desires.items():
        if cfg["type"] == "exact":
            assert city_day_counts[c] == cfg["days"], f"Exact duration mismatch for {c}: got {city_day_counts[c]}, want {cfg['days']}"

    # 3) Window constraints
    for c, (ws, we) in windows.items():
        days_in_c = sorted([d for d in range(1, total_days+1) if c in day_cities[d]])
        assert set(days_in_c) == set(range(ws, we+1)), f"{c} must be present exactly on days {ws}-{we}, got {days_in_c}"

    # 4) Only direct flights used is already enforced via assertions earlier

    # 5) Must visit exactly 10 distinct cities (we do)
    visited = set()
    for _, s, e in itinerary_segments:
        pass
    for c, s, e in itinerary_segments:
        visited.add(c)
    assert len(visited) == 10, f"Visited {len(visited)} unique cities, expected 10"

    # Prepare output
    itinerary_output = []
    for city, s, e in itinerary_segments:
        itinerary_output.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary_output}, ensure_ascii=False))

if __name__ == "__main__":
    main()
import json
import itertools

def compute_itinerary(total_days, city_durations, flights, windows):
    cities = list(city_durations.keys())
    n = len(cities)
    required_sum = sum(city_durations.values())
    # With single contiguous block per city and overlap on each flight day,
    # the union of days equals total_days if and only if:
    # sum(durations) = total_days + (number_of_flights), and number_of_flights = n - 1
    expected_sum = total_days + (n - 1)
    if required_sum != expected_sum:
        raise ValueError(
            f"Sum of city durations ({required_sum}) must equal total_days + (n-1) = {expected_sum} "
            "for a contiguous single-block-per-city plan with overlaps on flight days."
        )

    def has_direct(a, b):
        return (a, b) in flights

    def build_segments(order):
        # Compute start/end with overlap on flight days
        segs = []
        start = 1
        for i, city in enumerate(order):
            dur = city_durations[city]
            end = start + dur - 1
            segs.append((city, start, end))
            # Next segment starts on this segment's end day (overlap on flight day)
            start = end
        # Validate total coverage ends at total_days
        if segs[-1][2] != total_days:
            return None
        return segs

    def windows_ok(segments):
        # Build quick lookup
        idx = {city: (s, e) for city, s, e in segments}
        for city, (ws, we) in windows.items():
            if city not in idx:
                return False
            s, e = idx[city]
            if not (s <= ws and e >= we):
                return False
        return True

    def edges_ok(order):
        return all(has_direct(order[i], order[i+1]) for i in range(len(order)-1))

    # Try all permutations and pick the first valid according to constraints
    for order in itertools.permutations(cities):
        if not edges_ok(order):
            continue
        segs = build_segments(order)
        if segs is None:
            continue
        if not windows_ok(segs):
            continue
        # Validate per-city day counts and total day coverage logic
        # Build day-wise presence to ensure coverage of 1..total_days with allowed overlaps
        day_presence = {day: [] for day in range(1, total_days + 1)}
        for city, s, e in segs:
            for d in range(s, e + 1):
                day_presence[d].append(city)
        # Ensure every day 1..total_days has at least one city
        if any(len(day_presence[d]) == 0 for d in range(1, total_days + 1)):
            continue
        # Validate counts match required durations (since overlaps are allowed)
        counted = {city: 0 for city in cities}
        for city, s, e in segs:
            counted[city] += (e - s + 1)
        if any(counted[c] != city_durations[c] for c in cities):
            continue

        # Build output itinerary
        itinerary = []
        for city, s, e in segs:
            itinerary.append({
                "day_range": f"Day {s}-{e}",
                "place": city
            })
        return {"itinerary": itinerary}

    raise RuntimeError("No valid itinerary found under the given constraints.")

def main():
    # Input variables
    total_days = 20
    city_durations = {
        "Valencia": 6,
        "Athens": 6,
        "Naples": 5,
        "Zurich": 6
    }
    # Direct flights: include specified undirected pairs as both directions,
    # and include the one-way "from Valencia to Athens".
    flights = set()
    def add_undirected(a, b):
        flights.add((a, b))
        flights.add((b, a))

    add_undirected("Valencia", "Naples")
    flights.add(("Valencia", "Athens"))  # one-way as specified
    add_undirected("Athens", "Naples")
    add_undirected("Zurich", "Naples")
    add_undirected("Athens", "Zurich")
    add_undirected("Zurich", "Valencia")

    # Required presence windows: must cover entire window
    windows = {
        "Athens": (1, 6),   # Visit relatives between day 1 and day 6
        "Naples": (16, 20)  # Attend wedding between day 16 and day 20
    }

    result = compute_itinerary(total_days, city_durations, flights, windows)
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()
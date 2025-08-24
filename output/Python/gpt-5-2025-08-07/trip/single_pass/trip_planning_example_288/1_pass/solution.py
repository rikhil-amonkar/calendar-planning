import json
import itertools

def plan_trip():
    # Input variables
    total_days = 15
    cities = ["Stuttgart", "Manchester", "Madrid", "Vienna"]
    required_days = {
        "Stuttgart": 5,
        "Manchester": 7,
        "Madrid": 4,
        "Vienna": 2
    }
    # Fixed presence windows (inclusive)
    # Attending wedding in Manchester Day 1-7; workshop in Stuttgart Day 11-15
    fixed_windows = {
        "Manchester": (1, 7),
        "Stuttgart": (11, 15)
    }
    # Direct flight pairs (undirected)
    direct_pairs = [
        ("Vienna", "Stuttgart"),
        ("Manchester", "Vienna"),
        ("Madrid", "Vienna"),
        ("Manchester", "Stuttgart"),
        ("Manchester", "Madrid"),
    ]

    # Build adjacency map
    adj = {c: set() for c in cities}
    for a, b in direct_pairs:
        adj[a].add(b)
        adj[b].add(a)

    def has_direct(a, b):
        return b in adj.get(a, set())

    # Basic validations
    # Required overlaps needed to fit all city-days into total_days
    total_required = sum(required_days.values())
    overlaps_needed = total_required - total_days
    if overlaps_needed < 0:
        raise ValueError("Total required days are less than total trip days; underconstrained.")
    # Fixed windows must match required durations for those cities
    for city, (s, e) in fixed_windows.items():
        if required_days[city] != (e - s + 1):
            raise ValueError(f"Fixed window for {city} does not match its required days.")

    # Anchor cities (start and end based on fixed windows)
    start_city = "Manchester"
    start_range = fixed_windows[start_city]
    end_city = "Stuttgart"
    end_range = fixed_windows[end_city]

    if start_range[0] != 1 or end_range[1] != total_days:
        raise ValueError("Anchors must cover trip start and end days.")

    # Interior cities are those not fixed by windows
    interior_cities = [c for c in cities if c not in fixed_windows]

    # We seek a path: [start_city] + perm(interior_cities) + [end_city]
    # with direct flights between consecutive cities.
    # Additionally, we align durations so that:
    #   let M_end = start_range[1]
    #   let S_start = end_range[0]
    #   For interior cities X1..Xk, scheduled consecutively with
    #       X1.start = M_end,
    #       Xi.end = Xi.start + required_days[Xi] - 1,
    #       Xi+1.start = Xi.end,
    #   then we must have last_interior.end == S_start to align with end city start.
    M_end = start_range[1]
    S_start = end_range[0]

    def fits_time_alignment(order):
        # sum(required_days[Xi]) - len(order) must equal S_start - M_end
        D = sum(required_days[c] for c in order)
        k = len(order)
        return (D - k) == (S_start - M_end)

    def path_has_directs(order):
        seq = [start_city] + list(order) + [end_city]
        return all(has_direct(seq[i], seq[i+1]) for i in range(len(seq)-1))

    chosen_order = None
    for perm in itertools.permutations(interior_cities):
        if not path_has_directs(perm):
            continue
        if not fits_time_alignment(perm):
            continue
        chosen_order = list(perm)
        break

    if chosen_order is None:
        raise RuntimeError("No feasible sequence of cities satisfies direct flights and time alignment.")

    # Build segments with inclusive ranges and overlaps on flight days
    segments = []

    # Add start city (fixed)
    segments.append({"city": start_city, "start": start_range[0], "end": start_range[1]})

    # Build interior segments
    prev_end = segments[-1]["end"]
    for city in chosen_order:
        seg_start = prev_end  # flight occurs this day; counts for both prev and this city
        seg_end = seg_start + required_days[city] - 1
        segments.append({"city": city, "start": seg_start, "end": seg_end})
        prev_end = seg_end

    # Add end city (fixed) - ensure alignment
    if prev_end != end_range[0]:
        raise RuntimeError("Internal alignment failed unexpectedly.")
    segments.append({"city": end_city, "start": end_range[0], "end": end_range[1]})

    # Validate counts per city considering overlap rule
    # A day counts for a city if the day is within its segment [start, end].
    day_city_map = {city: set() for city in cities}
    for seg in segments:
        c = seg["city"]
        for d in range(seg["start"], seg["end"] + 1):
            day_city_map[c].add(d)

    # Check required day counts
    for c in cities:
        if len(day_city_map[c]) != required_days[c]:
            raise RuntimeError(f"City {c} has {len(day_city_map[c])} days, required {required_days[c]}.")

    # Check that overall days covered are within 1..total_days
    all_days = set()
    for d in range(1, total_days + 1):
        all_days.add(d)
    # Ensure that each day is covered by at least one city (it should be)
    for d in range(1, total_days + 1):
        if not any(seg["start"] <= d <= seg["end"] for seg in segments):
            raise RuntimeError(f"Day {d} is not allocated to any city.")

    # Build output itinerary (ordered)
    itinerary = []
    for seg in segments:
        itinerary.append({
            "day_range": f"Day {seg['start']}-{seg['end']}",
            "place": seg["city"]
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = plan_trip()
    print(json.dumps(result, ensure_ascii=False))
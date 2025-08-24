import json
from collections import defaultdict

def build_adjacency(flight_pairs):
    graph = defaultdict(set)
    for a, b in flight_pairs:
        graph[a].add(b)
        graph[b].add(a)
    return graph

def intersects(a1, b1, a2, b2):
    return not (b1 < a2 or b2 < a1)

def dfs_search(cities, durations, graph, fixed_start_days, must_cover_windows, must_intersect_windows):
    total_cities = len(cities)
    required_sum = sum(durations[c] for c in cities)
    # With overlap of one day at each transition, last day = sum(durs) - (n-1) = 28 by design
    assert required_sum - (total_cities - 1) == 28, "Durations do not align to 28 days with overlaps."

    city_set = set(cities)

    # Precompute anchored city lookup
    day_to_fixed_city = {start: city for city, (start, end) in must_cover_windows.items()}

    def recurse(sequence, used, current_start_day, last_city):
        # If we've placed all cities, verify final day is 28
        if len(sequence) == total_cities:
            # end_day of last segment
            end_day = current_start_day + durations[last_city] - 1
            if end_day != 28:
                return None
            # Validate intersect windows (Copenhagen) already checked during placement
            return sequence

        # If we passed day 15 and Copenhagen not yet placed, it's impossible to meet the meet-friend window
        if "Copenhagen" not in used and current_start_day > 15:
            return None

        # Forced placement on fixed start days (Naples=5, Athens=8, Mykonos=27)
        if current_start_day in day_to_fixed_city:
            forced_city = day_to_fixed_city[current_start_day]
            if forced_city in used:
                return None
            # adjacency check
            if last_city is not None and forced_city not in graph[last_city]:
                return None
            # compute end day
            end_day = current_start_day + durations[forced_city] - 1
            # Check must-cover window (should be satisfied by construction)
            fs, fe = must_cover_windows[forced_city]
            if not (current_start_day <= fs and end_day >= fe):
                return None
            # Check that we don't overstep any upcoming anchored start day
            for ad in day_to_fixed_city.keys():
                if ad > current_start_day and day_to_fixed_city[ad] not in used:
                    if end_day > ad:
                        return None
            # Check Copenhagen intersect window if forced city is Copenhagen (not the case, but for generality)
            if forced_city in must_intersect_windows:
                ws, we = must_intersect_windows[forced_city]
                if not intersects(current_start_day, end_day, ws, we):
                    return None
            sequence.append((forced_city, current_start_day, end_day))
            used.add(forced_city)
            # next start day is end_day due to overlap rule
            return recurse(sequence, used, end_day, forced_city)

        # Otherwise, try all candidates
        candidates = [c for c in cities if c not in used]
        # Sort candidates to improve chances: prioritize those that connect to last_city, shorter shifts first
        def cand_key(c):
            shift = durations[c] - 1
            conn = 0 if (last_city is None or c in graph[last_city]) else 1
            # Prefer earlier lexicographically for determinism as tie-breaker
            return (conn, shift, c)
        candidates.sort(key=cand_key)

        for city in candidates:
            # City with anchored start day cannot be placed unless at its exact start day
            if city in fixed_start_days and fixed_start_days[city] != current_start_day:
                continue

            # adjacency
            if last_city is not None and city not in graph[last_city]:
                continue

            # compute end day of this segment
            end_day = current_start_day + durations[city] - 1

            # Prune if this placement skips over any upcoming fixed start day
            skip_fixed = False
            for ad in sorted(day_to_fixed_city.keys()):
                if ad > current_start_day and day_to_fixed_city[ad] not in used:
                    if end_day > ad:
                        skip_fixed = True
                        break
            if skip_fixed:
                continue

            # must-cover windows (subset) check
            if city in must_cover_windows:
                ws, we = must_cover_windows[city]
                if not (current_start_day <= ws and end_day >= we):
                    continue

            # must-intersect windows (Copenhagen friend meet)
            if city in must_intersect_windows:
                ws, we = must_intersect_windows[city]
                if not intersects(current_start_day, end_day, ws, we):
                    continue

            # Place city
            sequence.append((city, current_start_day, end_day))
            used.add(city)
            res = recurse(sequence, used, end_day, city)
            if res is not None:
                return res
            # backtrack
            sequence.pop()
            used.remove(city)

        return None

    return recurse([], set(), 1, None)

def main():
    # Input variables (constraints)
    cities = [
        "Copenhagen", "Geneva", "Mykonos", "Naples", "Prague",
        "Dubrovnik", "Athens", "Santorini", "Brussels", "Munich"
    ]

    durations = {
        "Copenhagen": 5,
        "Geneva": 3,
        "Mykonos": 2,
        "Naples": 4,
        "Prague": 2,
        "Dubrovnik": 3,
        "Athens": 4,
        "Santorini": 5,
        "Brussels": 4,
        "Munich": 5
    }

    # Direct flight pairs (undirected)
    flight_pairs = [
        ("Copenhagen", "Dubrovnik"),
        ("Brussels", "Copenhagen"),
        ("Prague", "Geneva"),
        ("Athens", "Geneva"),
        ("Naples", "Dubrovnik"),
        ("Athens", "Dubrovnik"),
        ("Geneva", "Mykonos"),
        ("Naples", "Mykonos"),
        ("Naples", "Copenhagen"),
        ("Munich", "Mykonos"),
        ("Naples", "Athens"),
        ("Prague", "Athens"),
        ("Santorini", "Geneva"),
        ("Athens", "Santorini"),
        ("Naples", "Munich"),
        ("Prague", "Copenhagen"),
        ("Brussels", "Naples"),
        ("Athens", "Mykonos"),
        ("Athens", "Copenhagen"),
        ("Naples", "Geneva"),
        ("Dubrovnik", "Munich"),
        ("Brussels", "Munich"),
        ("Prague", "Brussels"),
        ("Brussels", "Athens"),
        ("Athens", "Munich"),
        ("Geneva", "Munich"),
        ("Copenhagen", "Munich"),
        ("Brussels", "Geneva"),
        ("Copenhagen", "Geneva"),
        ("Prague", "Munich"),
        ("Copenhagen", "Santorini"),
        ("Naples", "Santorini"),
        ("Geneva", "Dubrovnik"),
    ]

    graph = build_adjacency(flight_pairs)

    # Must cover exact windows (subset includes whole window)
    must_cover_windows = {
        "Naples": (5, 8),     # relatives visit window (and duration 4) -> start=5
        "Athens": (8, 11),    # workshop window (and duration 4) -> start=8
        "Mykonos": (27, 28),  # conference on days 27-28 (and duration 2) -> start=27
    }

    # For convenience, fixed starts derived from must_cover_windows
    fixed_start_days = {city: start for city, (start, end) in must_cover_windows.items()}

    # Must intersect windows (at least one day overlap)
    must_intersect_windows = {
        "Copenhagen": (11, 15)  # meet friend sometime between day 11 and 15
    }

    sequence = dfs_search(cities, durations, graph, fixed_start_days, must_cover_windows, must_intersect_windows)
    if sequence is None:
        raise RuntimeError("No feasible itinerary found under given constraints.")

    # Build itinerary output
    itinerary = []
    for city, start, end in sequence:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
import json

def build_adjacency(direct_flights):
    adj = {}
    for a, neighbors in direct_flights.items():
        adj.setdefault(a, set())
        for b in neighbors:
            adj[a].add(b)
            adj.setdefault(b, set()).add(a)
    return adj

def count_days_from_segments(segments):
    # segments: list of tuples (start_day, end_day, city)
    counts = {}
    for s, e, city in segments:
        counts[city] = counts.get(city, 0) + (e - s + 1)
    return counts

def unique_days_covered(segments):
    covered = set()
    for s, e, _ in segments:
        covered.update(range(s, e + 1))
    return covered

def find_itinerary(total_days, required_days, workshop_city, workshop_window, direct_flights):
    adj = build_adjacency(direct_flights)
    if workshop_city not in required_days:
        raise ValueError("Workshop city must be in required_days.")

    # Determine feasible Venice segment starts that cover the workshop window and fit in total_days
    K = required_days[workshop_city]
    w_start, w_end = workshop_window
    window_len = w_end - w_start + 1
    if K < window_len:
        raise ValueError("Required days in workshop city are fewer than workshop window length; impossible.")

    start_min = max(1, w_end - K + 1)  # earliest possible start that still covers workshop end
    start_max = min(w_start, total_days - K + 1)  # latest possible start that still fits and covers workshop start

    candidates = []
    for ven_start in range(start_min, start_max + 1):
        ven_end = ven_start + K - 1
        # We prefer itineraries that exactly end on total_days (cover the whole trip cleanly)
        ends_on_total = (ven_end == total_days)
        candidates.append((not ends_on_total, ven_start, ven_end))  # not ends_on_total so True sorts after False

    # Sort to prefer those that end exactly on total_days, then earlier starts
    candidates.sort()

    for _, ven_start, ven_end in candidates:
        # C3 is workshop_city (Venice)
        C3 = workshop_city
        # C2 must be a neighbor of Venice
        for C2 in adj.get(C3, []):
            if C2 not in required_days:
                continue
            # C1 must be a neighbor of C2 and distinct from Venice
            for C1 in adj.get(C2, []):
                if C1 == C3 or C1 not in required_days:
                    continue
                # Flight days (overlap days)
                d23 = ven_start  # C2 -> C3 on ven_start day
                # For exact required days, the following must hold:
                # len(C1) = d12
                # len(C2) = d23 - d12 + 1
                # len(C3) = K
                # unique days = sum(len(ci)) - number_of_flights (2) must equal total_days
                d12 = required_days[C1]
                if not (1 <= d12 <= d23):
                    continue
                if required_days[C2] != d23 - d12 + 1:
                    continue
                unique = required_days[C1] + required_days[C2] + required_days[C3] - 2
                if unique != total_days:
                    continue
                # Validate direct flights for the path C1->C2->C3
                if C2 not in adj.get(C1, set()):
                    continue
                if C3 not in adj.get(C2, set()):
                    continue
                # Build segments
                segments = [
                    (1, d12, C1),
                    (d12, d23, C2),
                    (d23, ven_end, C3),
                ]
                # Validate counts exactly
                counts = count_days_from_segments(segments)
                valid_counts = all(counts.get(city, 0) == req for city, req in required_days.items())
                if not valid_counts:
                    continue
                # Validate days covered are exactly 1..total_days
                covered = unique_days_covered(segments)
                if covered != set(range(1, total_days + 1)):
                    continue
                # Found a valid itinerary
                itinerary = []
                for s, e, city in sorted(segments, key=lambda x: x[0]):
                    itinerary.append({"day_range": f"Day {s}-{e}", "place": city})
                return {"itinerary": itinerary}

    raise ValueError("No valid itinerary could be found with the given constraints.")

if __name__ == "__main__":
    # Input variables (constraints)
    total_days = 10
    required_days = {
        "Venice": 6,
        "Mykonos": 2,
        "Vienna": 4
    }
    workshop_city = "Venice"
    workshop_window = (5, 10)  # inclusive

    direct_flights = {
        "Mykonos": ["Vienna"],
        "Vienna": ["Mykonos", "Venice"],
        "Venice": ["Vienna"]
    }

    result = find_itinerary(total_days, required_days, workshop_city, workshop_window, direct_flights)
    print(json.dumps(result, ensure_ascii=False))
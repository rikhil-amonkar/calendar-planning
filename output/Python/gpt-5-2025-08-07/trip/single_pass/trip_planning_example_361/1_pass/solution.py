import json
import itertools

def build_adjacency(direct_pairs):
    adj = {}
    for a, b in direct_pairs:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def compute_itinerary(total_days, cities, stay_requirements, direct_pairs, presence_windows):
    # Build adjacency for direct flights
    adj = build_adjacency(direct_pairs)

    # Validate inputs
    if set(stay_requirements.keys()) != set(cities):
        raise ValueError("Stay requirements must be specified for all cities listed.")

    # Flights needed equals overlap days required (sum of stays - total days)
    flights_needed = sum(stay_requirements.values()) - total_days
    if flights_needed < 0:
        raise ValueError("Total of required stays cannot be less than total days.")
    # At minimum visiting N cities requires at least N-1 flights; ensure consistency
    min_flights = len(cities) - 1
    if flights_needed != min_flights:
        # For these constraints with overlapping counts on flight days,
        # feasibility requires flights_needed == number of transitions (N-1)
        # Otherwise, it's impossible to meet exact per-city day counts.
        raise ValueError(f"Infeasible: required overlaps (sum(stays)-total_days={flights_needed}) "
                         f"must equal number of transitions ({min_flights}).")

    # Determine start and end via presence windows
    start_city = None
    end_city = None
    for city, (s, e) in presence_windows.items():
        if s == 1:  # must be present from day 1
            start_city = city
        if e == total_days:  # must be present through the last day
            end_city = city
    if not start_city or not end_city:
        raise ValueError("Presence windows must specify a start city covering Day 1 and an end city covering the last day.")

    # Start city's presence window should exactly match its required days (to avoid revisiting)
    start_window = presence_windows[start_city]
    if (start_window[1] - start_window[0] + 1) != stay_requirements[start_city]:
        raise ValueError("Start city's presence window must equal its required stay to avoid revisits.")
    # End city's presence window should exactly match its required days (to avoid arriving earlier)
    end_window = presence_windows[end_city]
    if (end_window[1] - end_window[0] + 1) != stay_requirements[end_city]:
        raise ValueError("End city's presence window must equal its required stay to avoid extra days.")

    # Intermediate cities are those not start or end
    intermediates = [c for c in cities if c not in (start_city, end_city)]

    # Precompute the required arrival day into the end city
    required_arrival_to_end = total_days - stay_requirements[end_city] + 1

    best_plan = None

    # Try all permutations of intermediate cities to find a feasible path with direct flights
    for order in itertools.permutations(intermediates):
        segments = []
        # Start segment: from Day 1 to end of presence window for start city
        start_seg_start = 1
        start_seg_end = presence_windows[start_city][1]
        segments.append({"city": start_city, "start_day": start_seg_start, "end_day": start_seg_end})

        # We must leave start_city on start_seg_end (flight day)
        current_city = start_city
        current_day = start_seg_end  # day of first flight and arrival to next city
        feasible = True

        # Validate flight from start to first intermediate
        if order:
            next_city = order[0]
            if next_city not in adj.get(current_city, set()):
                feasible = False

        # Build segments for intermediates
        for idx, city in enumerate(order):
            # Arrive on current_day, stay for required days
            stay_len = stay_requirements[city]
            seg_start = current_day
            seg_end = seg_start + stay_len - 1

            # Check direct flight from previous city to this city
            if city not in adj.get(current_city, set()):
                feasible = False
                break

            segments.append({"city": city, "start_day": seg_start, "end_day": seg_end})

            # Prepare for next hop
            current_city = city
            current_day = seg_end  # flight occurs on seg_end to next city (or to end city)

        if not feasible:
            continue

        # Now, we must fly to the end city on required_arrival_to_end
        # That means the last intermediate segment must end on required_arrival_to_end
        if segments[-1]["end_day"] != required_arrival_to_end:
            continue

        # Check direct flight from last intermediate (or start if no intermediates) to end city
        if end_city not in adj.get(current_city, set()):
            continue

        # Append end city segment: from arrival day to total_days
        segments.append({"city": end_city, "start_day": required_arrival_to_end, "end_day": total_days})

        # Verify flight count equals flights_needed (segments - 1)
        if len(segments) - 1 != flights_needed:
            continue

        # Verify per-city day counts using overlap rules
        # Build day -> set(cities) map
        day_to_cities = {d: set() for d in range(1, total_days + 1)}
        for seg in segments:
            for d in range(seg["start_day"], seg["end_day"] + 1):
                day_to_cities[d].add(seg["city"])

        # Count days per city
        counts = {c: 0 for c in cities}
        for d in range(1, total_days + 1):
            for c in day_to_cities[d]:
                counts[c] += 1

        # Validate counts
        if counts == stay_requirements:
            best_plan = segments
            break

    if not best_plan:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    # Prepare output in requested JSON structure
    itinerary = []
    for seg in best_plan:
        itinerary.append({
            "day_range": f"Day {seg['start_day']}-{seg['end_day']}",
            "place": seg["city"]
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    # Input variables (trip constraints)
    total_days = 15
    cities = ["Paris", "Madrid", "Bucharest", "Seville"]
    stay_requirements = {
        "Paris": 6,
        "Madrid": 7,
        "Bucharest": 2,
        "Seville": 3
    }
    # Direct flight pairs (undirected)
    direct_pairs = [
        ("Paris", "Bucharest"),
        ("Seville", "Paris"),
        ("Madrid", "Bucharest"),
        ("Madrid", "Paris"),
        ("Madrid", "Seville"),
    ]
    # Presence windows: inclusive ranges for required presence
    # - Attend Madrid show Day 1-7
    # - Visit relatives in Bucharest Day 14-15
    presence_windows = {
        "Madrid": (1, 7),
        "Bucharest": (14, 15)
    }

    result = compute_itinerary(total_days, cities, stay_requirements, direct_pairs, presence_windows)
    print(json.dumps(result, ensure_ascii=False))
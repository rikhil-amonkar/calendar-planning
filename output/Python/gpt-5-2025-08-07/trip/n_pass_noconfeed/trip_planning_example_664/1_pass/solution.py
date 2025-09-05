import json
from itertools import permutations

def main():
    # Input variables (constraints)
    total_days = 18
    cities = ["Tallinn", "Bucharest", "Seville", "Stockholm", "Munich", "Milan"]

    # Desired stays (days). "plan to stay" treated as hard; "would like" treated as desired targets.
    durations = {
        "Tallinn": 2,     # plan to stay 2 days (hard)
        "Bucharest": 4,   # plan to stay 4 days (hard)
        "Seville": 5,     # want 5 days (fits window)
        "Stockholm": 5,   # would like 5 days
        "Munich": 5,      # plan to stay 5 days (hard)
        "Milan": 2        # would like 2 days
    }

    # Event windows (inclusive)
    relatives_window = (1, 4)     # in Bucharest between day 1 and 4
    wedding_window = (4, 8)       # in Munich between day 4 and 8
    friends_window = (8, 12)      # in Seville between day 8 and 12

    # Direct flights (undirected edges)
    direct_edges = {
        frozenset(["Milan", "Stockholm"]),
        frozenset(["Munich", "Stockholm"]),
        frozenset(["Bucharest", "Munich"]),
        frozenset(["Munich", "Seville"]),
        frozenset(["Stockholm", "Tallinn"]),
        frozenset(["Munich", "Milan"]),
        frozenset(["Munich", "Tallinn"]),
        frozenset(["Seville", "Milan"])
    }

    def has_direct(a, b):
        return frozenset([a, b]) in direct_edges

    # Step 1: Schedule Bucharest to cover relatives between day 1-4 and 4 total days
    # Align Bucharest exactly to window [1,4]
    def schedule_exact_within_window(city, duration, window, earliest_start):
        ws, we = window
        # Prefer starting at max(earliest_start, ws) if it fits
        start = max(earliest_start, ws)
        end = start + duration - 1
        if end <= we:
            return start, end
        # Otherwise, align to end of window
        end = we
        start = end - duration + 1
        if start < ws:
            raise ValueError(f"Cannot fit {city} for {duration} days within window {window}")
        if start < earliest_start:
            raise ValueError(f"Cannot start {city} at or after day {earliest_start} and fit within window {window}")
        return start, end

    itinerary = []

    # Bucharest
    bu_start, bu_end = schedule_exact_within_window("Bucharest", durations["Bucharest"], relatives_window, 1)
    itinerary.append(("Bucharest", bu_start, bu_end))

    # Step 2: Schedule Munich to cover wedding between day 4-8 for full 5 days
    if not has_direct("Bucharest", "Munich"):
        raise ValueError("No direct flight Bucharest-Munich, cannot attend wedding as planned.")
    mu_start, mu_end = schedule_exact_within_window("Munich", durations["Munich"], wedding_window, bu_end)
    itinerary.append(("Munich", mu_start, mu_end))

    # Ensure we fly on mu_start (day4) to have overlap with Bucharest per rule
    if mu_start != bu_end:
        # If not aligned, try to align to overlap on bu_end while staying within window
        tentative_start = bu_end
        tentative_end = tentative_start + durations["Munich"] - 1
        if tentative_start >= wedding_window[0] and tentative_end <= wedding_window[1]:
            mu_start, mu_end = tentative_start, tentative_end
            itinerary[-1] = ("Munich", mu_start, mu_end)
        else:
            # Fall back to previously computed; it's still valid inside the window
            pass

    # Step 3: Schedule Seville to meet friends between day 8-12 and 5 total days
    if not has_direct("Munich", "Seville"):
        raise ValueError("No direct flight Munich-Seville, cannot meet friends as planned.")
    se_start, se_end = schedule_exact_within_window("Seville", durations["Seville"], friends_window, mu_end)
    itinerary.append(("Seville", se_start, se_end))
    if se_start != mu_end:
        # Try to align overlap on mu_end if feasible
        tentative_start = mu_end
        tentative_end = tentative_start + durations["Seville"] - 1
        if tentative_start >= friends_window[0] and tentative_end <= friends_window[1]:
            se_start, se_end = tentative_start, tentative_end
            itinerary[-1] = ("Seville", se_start, se_end)

    # Step 4: Plan remaining cities order using direct flights: Milan, Stockholm, Tallinn (found via DFS)
    remaining = ["Milan", "Stockholm", "Tallinn"]

    def find_path(start_city, remaining_cities):
        for perm in permutations(remaining_cities):
            ok = True
            prev = start_city
            for c in perm:
                if not has_direct(prev, c):
                    ok = False
                    break
                prev = c
            if ok:
                return list(perm)
        return None

    path = find_path("Seville", remaining)
    if not path:
        raise ValueError("Could not find a direct-flight path through remaining cities.")

    # Step 5: Assign days to remaining cities sequentially, overlapping on flight days
    prev_end = se_end
    prev_city = "Seville"
    segs = []
    for city in path:
        if not has_direct(prev_city, city):
            raise ValueError(f"No direct flight from {prev_city} to {city}.")
        start = prev_end  # fly on prev_end day; contributes to both cities
        end = start + durations[city] - 1
        segs.append((city, start, end))
        prev_city = city
        prev_end = end

    # Aggregate full itinerary
    itinerary.extend(segs)

    # Sanity checks
    # 1) We visited all 6 cities
    visited = {c for c, s, e in itinerary}
    if set(cities) - visited:
        raise ValueError("Not all cities were visited.")

    # 2) Transitions are direct flights
    prev_city = None
    prev_end = None
    for c, s, e in itinerary:
        if prev_city is not None:
            if not has_direct(prev_city, c):
                raise ValueError(f"Invalid transition: {prev_city} -> {c} has no direct flight.")
            # Check overlapping rule holds: flight day is prev_end (end of previous segment) == start of current segment
            if s != prev_end:
                # This should not happen due to how we scheduled
                raise ValueError(f"Flight day misalignment between {prev_city} and {c}: {prev_end} vs {s}")
        prev_city = c
        prev_end = e

    # 3) Calendar spans day 1 to total_days
    first_start = itinerary[0][1]
    last_end = itinerary[-1][2]
    if first_start != 1 or last_end != total_days:
        raise ValueError(f"Calendar coverage mismatch: starts at {first_start}, ends at {last_end}, expected 1..{total_days}.")

    # 4) Validate city day counts equal desired durations (using segment lengths)
    # Because of overlap rule we defined each city's segment as inclusive [start, end], which equals targeted durations
    for c, s, e in itinerary:
        expected = durations[c]
        actual = e - s + 1
        if actual != expected:
            raise ValueError(f"Duration mismatch for {c}: got {actual}, expected {expected}")

    # 5) Validate event windows coverage
    def segment_for(city_name):
        for c, s, e in itinerary:
            if c == city_name:
                return (s, e)
        return None

    bu_seg = segment_for("Bucharest")
    mu_seg = segment_for("Munich")
    se_seg = segment_for("Seville")

    # Bucharest must lie within relatives window
    if not (bu_seg[0] >= relatives_window[0] and bu_seg[1] <= relatives_window[1]):
        raise ValueError("Bucharest segment does not fit within relatives window.")
    # Munich must overlap wedding window
    if mu_seg[1] < wedding_window[0] or mu_seg[0] > wedding_window[1]:
        raise ValueError("Munich segment does not overlap wedding window.")
    # Seville must overlap friends window
    if se_seg[1] < friends_window[0] or se_seg[0] > friends_window[1]:
        raise ValueError("Seville segment does not overlap friends window.")

    # Format output
    output = {
        "itinerary": [
            {"day_range": f"Day {s}-{e}", "place": c}
            for (c, s, e) in itinerary
        ]
    }
    print(json.dumps(output))

if __name__ == "__main__":
    main()
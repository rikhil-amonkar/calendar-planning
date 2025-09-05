import json
from itertools import permutations

def compute_itinerary():
    # Input variables (constraints)
    total_days = 12
    cities = ["Prague", "Berlin", "Tallinn", "Stockholm"]
    durations = {
        "Prague": 2,
        "Berlin": 3,
        "Tallinn": 5,
        "Stockholm": 5
    }
    # Direct flights (undirected)
    direct_flights = {
        frozenset(["Berlin", "Tallinn"]),
        frozenset(["Prague", "Tallinn"]),
        frozenset(["Stockholm", "Tallinn"]),
        frozenset(["Prague", "Stockholm"]),
        frozenset(["Stockholm", "Berlin"])
    }

    # Special day constraints
    must_be_in_berlin_days = {6, 8}  # conference on day 6 and day 8
    # Tallinn relatives visit "between day 8 and day 12" -> interpreted as being in Tallinn for days 8-12 inclusive
    tallinn_must_cover_days = set(range(8, 13))  # {8,9,10,11,12}

    # Helper to check if a contiguous segment [start, start+L-1] contains all required days
    def segment_covers_days(start, length, required_days):
        end = start + length - 1
        for d in required_days:
            if not (start <= d <= end):
                return False
        return True

    # Determine Tallinn segment (fixed by relatives constraint)
    L_tal = durations["Tallinn"]
    tallinn_candidates = []
    for s in range(1, total_days - L_tal + 2):
        if segment_covers_days(s, L_tal, tallinn_must_cover_days):
            tallinn_candidates.append((s, s + L_tal - 1))
    # Expect exactly one candidate: start 8, end 12
    if not tallinn_candidates:
        raise ValueError("No feasible Tallinn segment satisfies relatives visit constraint.")
    tallinn_start, tallinn_end = tallinn_candidates[0]

    # Determine Berlin segment: must include days 6 and 8, and end must align with Tallinn start (overlap flight day)
    L_ber = durations["Berlin"]
    berlin_candidates = []
    for s in range(1, total_days - L_ber + 2):
        e = s + L_ber - 1
        if segment_covers_days(s, L_ber, must_be_in_berlin_days) and e == tallinn_start:
            berlin_candidates.append((s, e))
    if not berlin_candidates:
        raise ValueError("No feasible Berlin segment satisfies conference days and connection to Tallinn.")
    berlin_start, berlin_end = berlin_candidates[0]

    # Remaining cities must be arranged before Berlin in two contiguous segments,
    # with overlaps on flight days: start_next = end_prev
    remaining = [c for c in cities if c not in ("Berlin", "Tallinn")]

    def has_direct(a, b):
        return frozenset([a, b]) in direct_flights

    best_plan = None

    for order in permutations(remaining):
        # order[0] -> order[1] -> Berlin -> Tallinn
        c1, c2 = order[0], order[1]

        # Check direct flights in the intended sequence
        if not has_direct(c2, "Berlin"):
            continue
        if not has_direct("Berlin", "Tallinn"):
            continue
        if not has_direct(c1, c2):
            continue

        # Back-calculate segment bounds using overlaps on flight days:
        # c2 ends on berlin_start (flight day), c2_start = end - L + 1
        L2 = durations[c2]
        c2_end = berlin_start
        c2_start = c2_end - L2 + 1

        # c1 ends on c2_start (flight day), c1_start = end - L + 1
        L1 = durations[c1]
        c1_end = c2_start
        c1_start = c1_end - L1 + 1

        # Validate bounds
        if c1_start < 1:
            continue

        # Validate total coverage equals total_days:
        # With 4 segments and 3 overlaps (flight days), union days should be sum(L) - 3
        sum_lengths = durations[c1] + durations[c2] + durations["Berlin"] + durations["Tallinn"]
        union_days = sum_lengths - 3
        if union_days != total_days:
            continue

        # Also ensure final end is total_days and initial start is Day 1
        # Final end is tallinn_end; it should be total_days by design from constraints
        if tallinn_end != total_days:
            continue
        if c1_start != 1:
            continue

        # All constraints satisfied; record plan
        segments = [
            (c1, c1_start, c1_end),
            (c2, c2_start, c2_end),
            ("Berlin", berlin_start, berlin_end),
            ("Tallinn", tallinn_start, tallinn_end),
        ]
        best_plan = segments
        break

    if best_plan is None:
        raise ValueError("No feasible itinerary found with given constraints and direct flights.")

    itinerary = []
    for city, start, end in best_plan:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result))
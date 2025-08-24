import json
import itertools

def compute_itinerary():
    # Input variables (trip constraints)
    total_days = 15
    cities_to_visit = ["Stuttgart", "Seville", "Manchester"]
    desired_days = {
        "Stuttgart": 6,
        "Seville": 7,
        "Manchester": 4
    }
    # Direct flights (bidirectional)
    direct_flight_pairs = [
        ("Manchester", "Seville"),
        ("Stuttgart", "Manchester")
    ]
    # Meeting constraint in Stuttgart: between day 1 and day 6 inclusive
    meet_city = "Stuttgart"
    meet_window = (1, 6)

    # Build adjacency set for quick direct-flight lookup
    direct_edges = set()
    for a, b in direct_flight_pairs:
        direct_edges.add((a, b))
        direct_edges.add((b, a))

    # Basic feasibility checks
    if set(desired_days.keys()) != set(cities_to_visit):
        raise ValueError("Desired days must be specified for exactly the cities to visit.")
    if sum(desired_days.values()) != total_days + 2:  # two flights -> two overlap days
        raise ValueError("Sum of desired days must equal total days plus number of flights (2).")

    def has_direct(u, v):
        return (u, v) in direct_edges

    def intersects(a, b):
        return max(a[0], b[0]) <= min(a[1], b[1])

    def intersection(a, b):
        if not intersects(a, b):
            return None
        return (max(a[0], b[0]), min(a[1], b[1]))

    candidates = []

    # Try all orderings that form a valid path with direct flights
    for order in itertools.permutations(cities_to_visit, 3):
        A, B, C = order
        # Must be able to fly A->B and B->C directly
        if not (has_direct(A, B) and has_direct(B, C)):
            continue

        # Compute flight days (inclusive overlap on flight day):
        # A covers Day 1..d1, B covers Day d1..d2, C covers Day d2..T
        d1 = desired_days[A]
        d2 = d1 + desired_days[B] - 1

        # Validate bounds
        if not (1 <= d1 <= total_days and d1 <= d2 <= total_days):
            continue

        # Check C's days match
        days_C = total_days - d2 + 1
        if days_C != desired_days[C]:
            continue

        # Meeting constraint for Stuttgart
        ranges = {
            A: (1, d1),
            B: (d1, d2),
            C: (d2, total_days)
        }
        stuttgart_range = ranges[meet_city]
        meet_int = intersection(stuttgart_range, meet_window)
        if meet_int is None:
            continue

        # Evaluate "optimality": earliest possible meeting day
        earliest_meet_day = meet_int[0]

        candidates.append({
            "order": order,
            "ranges": ranges,
            "d1": d1,
            "d2": d2,
            "earliest_meet_day": earliest_meet_day
        })

    if not candidates:
        # If no plan fits all constraints, return an empty itinerary to stay JSON-valid
        return {"itinerary": []}

    # Choose the candidate with earliest meeting day; tie-break by lexicographic order of order
    candidates.sort(key=lambda c: (c["earliest_meet_day"], c["order"]))
    best = candidates[0]
    A, B, C = best["order"]
    ranges = best["ranges"]

    def fmt_range(r):
        return f"Day {r[0]}-{r[1]}"

    itinerary = [
        {"day_range": fmt_range(ranges[A]), "place": A},
        {"day_range": fmt_range(ranges[B]), "place": B},
        {"day_range": fmt_range(ranges[C]), "place": C},
    ]
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result))
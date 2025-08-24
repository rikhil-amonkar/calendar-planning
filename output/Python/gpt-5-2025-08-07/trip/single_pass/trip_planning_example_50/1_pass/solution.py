import json
import itertools

def compute_itinerary():
    # Input variables (trip constraints)
    total_days = 12
    required_days = {
        "Vilnius": 4,
        "Munich": 3,
        "Mykonos": 7
    }
    cities = list(required_days.keys())

    # Direct flights:
    # - Between Munich and Mykonos (both directions)
    # - From Vilnius to Munich
    direct_flights = {
        ("Munich", "Mykonos"),
        ("Mykonos", "Munich"),
        ("Vilnius", "Munich")
    }

    # Number of flight days (overlap days) required by the durations
    flights_required = sum(required_days.values()) - total_days

    def is_direct(a, b):
        return (a, b) in direct_flights

    # Try all orders of visiting the 3 cities with exactly 2 flights (A->B->C)
    # Using the overlap rule, if on day f1 A->B and on day f2 B->C:
    # - A covers day 1..f1 inclusive -> f1 == required[A]
    # - B covers day f1..f2 inclusive -> (f2 - f1 + 1) == required[B]
    # - C covers day f2..total_days inclusive -> (total_days - f2 + 1) == required[C]
    # Solve:
    #   f1 = required[A]
    #   f2 = required[B] + f1 - 1
    # And check the third equation holds.
    solution = None

    for order in itertools.permutations(cities, 3):
        A, B, C = order
        if not (is_direct(A, B) and is_direct(B, C)):
            continue

        rA, rB, rC = required_days[A], required_days[B], required_days[C]

        # For a 3-city chain, flights_required must be 2 so that sums align.
        if flights_required != 2:
            continue

        f1 = rA
        f2 = rB + f1 - 1

        # Validate ranges
        if not (1 <= f1 < f2 <= total_days):
            continue

        # Validate C's required days are satisfied
        if (total_days - f2 + 1) != rC:
            continue

        # Build itinerary segments with overlaps on flight days
        itinerary_segments = [
            {"day_range": f"Day 1-{f1}", "place": A},
            {"day_range": f"Day {f1}-{f2}", "place": B},
            {"day_range": f"Day {f2}-{total_days}", "place": C},
        ]

        # Optional: verify by counting per-city days using overlap rule
        counts = {city: 0 for city in cities}
        for day in range(1, total_days + 1):
            if 1 <= day <= f1:
                counts[A] += 1
            if f1 <= day <= f2:
                counts[B] += 1
            if f2 <= day <= total_days:
                counts[C] += 1

        if counts == required_days:
            solution = itinerary_segments
            break

    # Fallback if no solution found
    if solution is None:
        solution = []

    return {"itinerary": solution}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))
import json
import itertools

def compute_itinerary():
    # Input variables (trip constraints)
    total_days = 23
    cities = ["Paris", "Oslo", "Porto", "Geneva", "Reykjavik"]
    durations = {
        "Paris": 6,
        "Oslo": 5,
        "Porto": 7,
        "Geneva": 7,
        "Reykjavik": 2,
    }

    # Direct flight connections (undirected)
    direct_pairs = [
        ("Paris", "Oslo"),
        ("Geneva", "Oslo"),
        ("Porto", "Paris"),
        ("Geneva", "Paris"),
        ("Geneva", "Porto"),
        ("Paris", "Reykjavik"),
        ("Reykjavik", "Oslo"),
        ("Porto", "Oslo"),
    ]

    # Build adjacency map
    adj = {c: set() for c in cities}
    for a, b in direct_pairs:
        adj[a].add(b)
        adj[b].add(a)

    # Hard constraints
    start_city = "Geneva"
    start_must_include_days = {1, 7}  # Conference in Geneva on day 1 and day 7
    end_city = "Oslo"
    oslo_fixed_start, oslo_fixed_end = 19, 23  # Visit relatives in Oslo between day 19 and 23

    # Verify total days consistency via overlap math
    required_flights = sum(durations.values()) - total_days
    if required_flights != len(cities) - 1:
        raise ValueError("Inconsistent durations vs total_days for a single-chain itinerary with overlaps.")

    if start_city not in cities or end_city not in cities:
        raise ValueError("Start or end city not in cities list.")

    # Helper to compute contiguous ranges with overlap on flight days
    def compute_ranges(order):
        ranges = {}
        start_day = 1
        prev_end = None
        for idx, city in enumerate(order):
            if idx == 0:
                s = start_day
            else:
                s = prev_end  # Flight day counts for both cities
            e = s + durations[city] - 1
            ranges[city] = (s, e)
            prev_end = e
        return ranges

    # Validate constraints for a given order
    def valid_order(order):
        # Check direct flights for consecutive cities
        for a, b in zip(order, order[1:]):
            if b not in adj[a]:
                return False

        # Compute day ranges
        ranges = compute_ranges(order)

        # Start city (Geneva) must include days 1 and 7
        g_s, g_e = ranges[start_city]
        if not (g_s <= 1 <= g_e and g_s <= 7 <= g_e):
            return False

        # Geneva must be exactly 7 days long
        if (g_e - g_s + 1) != durations[start_city]:
            return False

        # End city (Oslo) must be day 19-23 inclusive and exactly 5 days
        o_s, o_e = ranges[end_city]
        if not (o_s == oslo_fixed_start and o_e == oslo_fixed_end):
            return False

        # Total coverage must end on day 23
        if max(e for (_, e) in ranges.values()) != total_days:
            return False

        # Verify each city duration matches requested when counting overlaps
        for c in cities:
            s, e = ranges[c]
            if (e - s + 1) != durations[c]:
                return False

        return True

    # Build all possible orders: start -> perm(middle) -> end
    middle_cities = [c for c in cities if c not in (start_city, end_city)]
    feasible_order = None
    for perm in itertools.permutations(sorted(middle_cities)):
        order = [start_city] + list(perm) + [end_city]
        if valid_order(order):
            feasible_order = order
            break

    if feasible_order is None:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    # Compute final ranges
    ranges = compute_ranges(feasible_order)

    # Format itinerary in required JSON structure
    itinerary = []
    for city in feasible_order:
        s, e = ranges[city]
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))
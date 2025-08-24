import itertools
import json

def main():
    # Input variables (constraints)
    total_days = 20
    cities = ["Hamburg", "Munich", "Manchester", "Lyon", "Split"]
    required_days = {
        "Hamburg": 7,
        "Munich": 6,
        "Manchester": 2,
        "Lyon": 2,
        "Split": 7,
    }
    # Pinned day constraints (inclusive). Must be within the city's stay.
    pinned_days = {
        "Lyon": [13, 14],        # Show on days 13-14
        "Manchester": [19, 20],  # Visit relatives days 19-20 (end of trip)
    }

    # Flights: undirected for "A and B", plus explicitly directed from "Manchester to Split"
    undirected_pairs = [
        ("Split", "Munich"),
        ("Munich", "Manchester"),
        ("Hamburg", "Manchester"),
        ("Hamburg", "Munich"),
        ("Split", "Lyon"),
        ("Lyon", "Munich"),
        ("Hamburg", "Split"),
    ]
    directed_pairs = [
        ("Manchester", "Split"),  # explicitly directed
    ]

    # Build adjacency (directed)
    adj = {c: set() for c in cities}
    for a, b in undirected_pairs:
        adj[a].add(b)
        adj[b].add(a)
    for a, b in directed_pairs:
        adj.setdefault(a, set()).add(b)

    def has_direct(a, b):
        return b in adj.get(a, set())

    # Helper to compute start/end days for a given order, respecting overlaps (flight days)
    def compute_schedule(order):
        # Number of blocks
        n = len(order)
        # Sum of required days across all cities
        S = sum(required_days[c] for c in order)
        # Start day for the first city derived from total_days coverage
        # end_of_last = s1 + S - n
        # enforce end_of_last == total_days => s1 = total_days - (S - n)
        s1 = total_days - (S - n)
        if s1 < 1:
            return None  # invalid

        starts = {}
        ends = {}
        starts[order[0]] = s1
        ends[order[0]] = starts[order[0]] + required_days[order[0]] - 1
        for i in range(1, n):
            prev = order[i - 1]
            cur = order[i]
            # Overlap one day at flight: start(cur) = start(prev) + days(prev) - 1
            starts[cur] = starts[prev] + required_days[prev] - 1
            ends[cur] = starts[cur] + required_days[cur] - 1

        # Validate last end equals total_days
        if ends[order[-1]] != total_days:
            return None

        # Validate adjacencies are direct flights
        for i in range(1, n):
            if not has_direct(order[i - 1], order[i]):
                return None

        # Validate pinned day constraints
        for city, days in pinned_days.items():
            if city not in starts:
                return None
            lo, hi = min(days), max(days)
            if not (starts[city] <= lo and hi <= ends[city]):
                return None

        # All constraints satisfied
        return starts, ends

    # Additional pruning: any city that must include day 20 should be last in the order
    must_be_last = set()
    for city, days in pinned_days.items():
        if max(days) == total_days:
            must_be_last.add(city)

    valid_itinerary = None
    for order in itertools.permutations(cities):
        # Prune: enforce must-be-last
        if any(order[-1] != c for c in must_be_last):
            continue

        # Compute schedule for this order
        res = compute_schedule(order)
        if res is None:
            continue
        starts, ends = res

        # Verify total city-days accounting rule (sum of city days = total_days + number_of_flights)
        sum_city_days = sum(required_days[c] for c in order)
        flights_count = len(order) - 1
        if sum_city_days != total_days + flights_count:
            continue

        # Build itinerary output
        itinerary = []
        for c in order:
            itinerary.append({
                "day_range": f"Day {starts[c]}-{ends[c]}",
                "place": c
            })
        valid_itinerary = itinerary
        break

    if valid_itinerary is None:
        raise RuntimeError("No valid itinerary found under given constraints.")

    output = {"itinerary": valid_itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()
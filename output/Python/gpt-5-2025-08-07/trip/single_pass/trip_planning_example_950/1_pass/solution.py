import json
import itertools

def main():
    # Trip constraints
    total_days = 17
    cities = ["Rome", "Mykonos", "Nice", "Riga", "Bucharest", "Munich", "Krakow"]
    durations = {
        "Mykonos": 3,
        "Riga": 3,
        "Munich": 4,
        "Bucharest": 4,
        "Rome": 4,
        "Nice": 3,
        "Krakow": 2,
    }
    # Required presence constraints (inclusive days)
    required_days = {
        "Rome": {1, 4},
        "Mykonos": {4, 5, 6},
        "Krakow": {16, 17},
    }

    # Direct flights: "A and B" are bidirectional; "from A to B" are directed A->B
    bidirectional_pairs = [
        ("Nice", "Riga"),
        ("Bucharest", "Munich"),
        ("Mykonos", "Munich"),
        ("Riga", "Bucharest"),
        ("Rome", "Nice"),
        ("Rome", "Munich"),
        ("Mykonos", "Nice"),
        ("Rome", "Mykonos"),
        ("Munich", "Krakow"),
        ("Rome", "Bucharest"),
        ("Nice", "Munich"),
    ]
    directed_pairs = [
        ("Riga", "Munich"),
        ("Rome", "Riga"),
    ]

    # Build adjacency (directed)
    adj = {c: set() for c in cities}
    for a, b in bidirectional_pairs:
        adj[a].add(b)
        adj[b].add(a)
    for a, b in directed_pairs:
        adj[a].add(b)

    # Basic feasibility checks
    if set(durations.keys()) != set(cities):
        raise ValueError("Durations must be provided for all cities.")
    sum_city_days = sum(durations.values())
    # To satisfy total days with overlaps, we need exactly (sum_city_days - total_days) flight days
    required_flights = sum_city_days - total_days
    if required_flights < 0:
        raise ValueError("Impossible: city-day requirements are less than total trip days.")
    # With N cities, visiting each once in sequence means (N-1) flights.
    if required_flights != (len(cities) - 1):
        raise ValueError("Impossible: required overlaps (flight days) don't match number of city transitions.")

    # We must place:
    # - Rome first with Day 1 and Day 4 included (duration 4) -> fixed at Day 1-4
    # - Mykonos next to overlap on Day 4, and must be 3 days -> fixed to Day 4-6
    # - Krakow must be last and include Days 16-17 (duration 2) -> will be last by construction
    # Additionally, because only Munich has a direct flight to Krakow, Munich must be the city before Krakow.
    first = "Rome"
    second = "Mykonos"
    last = "Krakow"
    penultimate = "Munich"

    middle_candidates = [c for c in cities if c not in {first, second, penultimate, last}]

    def valid_path(order):
        # Check all consecutive legs are direct flights
        for a, b in zip(order[:-1], order[1:]):
            if b not in adj.get(a, set()):
                return False
        return True

    def compute_day_ranges(order, durations):
        # Overlap exactly one day between consecutive cities
        # City 1: Day 1..d1
        ranges = {}
        start = 1
        for i, city in enumerate(order):
            end = start + durations[city] - 1
            ranges[city] = (start, end)
            # Next city will overlap the 'end' day
            start = end
        return ranges

    def days_in_range(r):
        s, e = r
        return set(range(s, e + 1))

    solution_order = None
    solution_ranges = None

    # Search feasible permutations for the 3 middle cities
    for perm in itertools.permutations(middle_candidates):
        order = [first, second] + list(perm) + [penultimate, last]
        # 1) Flight feasibility
        if not valid_path(order):
            continue
        # 2) Compute day ranges based on required overlaps
        ranges = compute_day_ranges(order, durations)
        # 3) End day must be total_days (by construction it should be)
        if ranges[last][1] != total_days:
            continue
        # 4) Check required day presence for specified cities
        ok = True
        for city, req_days in required_days.items():
            city_days = days_in_range(ranges[city])
            if not req_days.issubset(city_days):
                ok = False
                break
        # 5) Ensure Munich is penultimate and direct to Krakow (already in order and adjacency check)
        if order[-2] != penultimate:
            ok = False
        # 6) Ensure conference/wedding/show alignment (already encoded in required_days)
        if ok:
            solution_order = order
            solution_ranges = ranges
            break

    if not solution_order:
        raise RuntimeError("No feasible itinerary found under given constraints.")

    # Produce itinerary JSON
    itinerary = []
    for city in solution_order:
        s, e = solution_ranges[city]
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
import json
import itertools

def main():
    # Input variables
    total_days = 22
    cities = [
        "Brussels", "Helsinki", "Split", "Dubrovnik",
        "Istanbul", "Milan", "Vilnius", "Frankfurt"
    ]
    desired_days = {
        "Brussels": 3,
        "Helsinki": 3,
        "Split": 4,
        "Dubrovnik": 2,
        "Istanbul": 5,
        "Milan": 4,
        "Vilnius": 5,
        "Frankfurt": 3
    }
    # Event constraints (inclusive day ranges)
    events = {
        "Istanbul": (1, 5),    # Show days 1-5
        "Frankfurt": (16, 18), # Wedding days 16-18
        "Vilnius": (18, 22)    # Workshop days 18-22
    }

    # Build directed adjacency (direct flights only)
    adjacency = {c: set() for c in cities}
    def add_undirected(a, b):
        adjacency[a].add(b)
        adjacency[b].add(a)
    def add_directed(a, b):
        adjacency[a].add(b)

    add_undirected("Milan", "Frankfurt")
    add_undirected("Split", "Frankfurt")
    add_undirected("Milan", "Split")
    add_undirected("Brussels", "Vilnius")
    add_undirected("Brussels", "Helsinki")
    add_undirected("Istanbul", "Brussels")
    add_undirected("Milan", "Vilnius")
    add_undirected("Brussels", "Milan")
    add_undirected("Istanbul", "Helsinki")
    add_undirected("Helsinki", "Vilnius")
    add_undirected("Helsinki", "Dubrovnik")
    add_undirected("Split", "Vilnius")
    add_directed("Dubrovnik", "Istanbul")  # one-way
    add_undirected("Istanbul", "Milan")
    add_undirected("Helsinki", "Frankfurt")
    add_undirected("Istanbul", "Vilnius")
    add_undirected("Split", "Helsinki")
    add_undirected("Milan", "Helsinki")
    add_undirected("Istanbul", "Frankfurt")
    add_directed("Brussels", "Frankfurt")  # one-way
    add_undirected("Dubrovnik", "Frankfurt")
    add_undirected("Frankfurt", "Vilnius")

    # Fixed cities for start/middle/end due to events
    start_city = "Istanbul"
    penultimate_city = "Frankfurt"
    end_city = "Vilnius"

    # Mid cities to arrange between Istanbul and Frankfurt
    mid_cities = ["Brussels", "Milan", "Split", "Helsinki", "Dubrovnik"]

    # Helper: check if a sequence is feasible regarding direct flights
    def feasible_sequence(seq):
        # Start from Istanbul to first mid city
        if seq:
            if seq[0] not in adjacency[start_city]:
                return False
        # Between mid cities
        for a, b in zip(seq, seq[1:]):
            if b not in adjacency[a]:
                return False
        # Last mid city to Frankfurt
        if seq:
            if penultimate_city not in adjacency[seq[-1]]:
                return False
        # Frankfurt to Vilnius
        if end_city not in adjacency[penultimate_city]:
            return False
        return True

    # Search for a feasible order of mid cities
    mid_sequence = None
    # Bias order so a likely-valid chain is tried first; still algorithmic via permutations
    candidate_order = mid_cities[:]  # ["Brussels","Milan","Split","Helsinki","Dubrovnik"]
    for perm in itertools.permutations(candidate_order):
        if feasible_sequence(perm):
            mid_sequence = list(perm)
            break

    if mid_sequence is None:
        # If no valid sequence, output an error JSON (should not happen with given constraints)
        print(json.dumps({"error": "No feasible itinerary found with given constraints"}))
        return

    # Construct full path
    path = [start_city] + mid_sequence + [penultimate_city, end_city]

    # Compute start days for each city along the path based on desired durations and overlap rule:
    # If fly from A to B on day X, both A and B include day X.
    # Recurrence: start[next] = start[current] + days[current] - 1
    start_day = {start_city: 1}
    for i in range(len(path) - 1):
        cur = path[i]
        nxt = path[i + 1]
        start_day[nxt] = start_day[cur] + desired_days[cur] - 1

    # Compute end day for last city
    last_city = path[-1]
    end_last = start_day[last_city] + desired_days[last_city] - 1

    # Validate totals and event windows
    assert end_last == total_days, "End day must match total_days"

    # Build occupancy sets per city
    occupancy = {c: set() for c in path}
    for i in range(len(path) - 1):
        cur = path[i]
        nxt = path[i + 1]
        for d in range(start_day[cur], start_day[nxt] + 1):
            occupancy[cur].add(d)
    # Last city occupies its own full range
    for d in range(start_day[last_city], end_last + 1):
        occupancy[last_city].add(d)

    # Verify desired day counts match
    for c in path:
        if len(occupancy[c]) != desired_days[c]:
            raise AssertionError(f"City {c} has {len(occupancy[c])} days, expected {desired_days[c]}")

    # Verify event windows
    for c, (lo, hi) in events.items():
        for d in range(lo, hi + 1):
            if d not in occupancy[c]:
                raise AssertionError(f"Event constraint violated: {c} must include day {d}")

    # Format itinerary as day ranges per city in travel order
    itinerary = []
    for i, c in enumerate(path):
        if i < len(path) - 1:
            start = start_day[c]
            end = start_day[path[i + 1]]
        else:
            start = start_day[c]
            end = start + desired_days[c] - 1
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": c
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
import json
import itertools

def build_adjacency(edges):
    adj = {}
    for a, b in edges:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def compute_day_ranges(order, durations, total_days):
    # Using the rule: departure flight occurs on the last day in each city,
    # and that day counts for both the origin and destination city.
    ranges = {}
    start_day = 1
    for i, city in enumerate(order):
        d = durations[city]
        end_day = start_day + d - 1
        ranges[city] = (start_day, end_day)
        start_day = end_day  # next city starts on the same day due to overlap
    # Validate final end day matches total_days
    final_end = ranges[order[-1]][1]
    return ranges if final_end == total_days else None

def is_direct_path(order, adj):
    return all(order[i+1] in adj.get(order[i], set()) for i in range(len(order)-1))

def satisfies_constraints(ranges, special_constraints):
    # Show in Barcelona days 1-3
    bcn_start, bcn_end = ranges["Barcelona"]
    if not (bcn_start <= 1 and bcn_end >= 3):
        return False
    # Oslo between day 3 and day 4 (be in Oslo on those days)
    osl_start, osl_end = ranges["Oslo"]
    if not (osl_start <= 3 <= osl_end and osl_start <= 4 <= osl_end):
        return False
    # Brussels meeting between day 9 and day 11 (be in Brussels on at least one of those days)
    bru_start, bru_end = ranges["Brussels"]
    if not any(bru_start <= d <= bru_end for d in range(9, 12)):
        return False
    return True

def verify_durations(ranges, durations):
    for city, (s, e) in ranges.items():
        if e - s + 1 != durations[city]:
            return False
    return True

def main():
    # Input variables
    total_trip_days = 16
    durations = {
        "Oslo": 2,
        "Stuttgart": 3,
        "Venice": 4,
        "Split": 4,
        "Barcelona": 3,
        "Brussels": 3,
        "Copenhagen": 3
    }
    # Direct flight pairs (undirected)
    direct_pairs = [
        ("Venice", "Stuttgart"),
        ("Oslo", "Brussels"),
        ("Split", "Copenhagen"),
        ("Barcelona", "Copenhagen"),
        ("Barcelona", "Venice"),
        ("Brussels", "Venice"),
        ("Barcelona", "Stuttgart"),
        ("Copenhagen", "Brussels"),
        ("Oslo", "Split"),
        ("Oslo", "Venice"),
        ("Barcelona", "Split"),
        ("Oslo", "Copenhagen"),
        ("Barcelona", "Oslo"),
        ("Copenhagen", "Stuttgart"),
        ("Split", "Stuttgart"),
        ("Copenhagen", "Venice"),
        ("Barcelona", "Brussels"),
    ]
    adj = build_adjacency(direct_pairs)

    cities = list(durations.keys())
    # Must start in Barcelona to attend the show on days 1-3
    # Oslo must be second to ensure presence on day 3-4 with a 2-day stay
    fixed_start = ["Barcelona", "Oslo"]
    remaining = [c for c in cities if c not in fixed_start]

    found_order = None
    found_ranges = None

    for perm in itertools.permutations(remaining):
        order = fixed_start + list(perm)
        # Check direct flights constraint
        if not is_direct_path(order, adj):
            continue
        # Compute day ranges with overlap rule
        ranges = compute_day_ranges(order, durations, total_trip_days)
        if ranges is None:
            continue
        # Verify exact durations
        if not verify_durations(ranges, durations):
            continue
        # Verify special constraints
        if not satisfies_constraints(ranges, special_constraints=None):
            continue
        # All constraints satisfied
        found_order = order
        found_ranges = ranges
        break

    if not found_order:
        print(json.dumps({"error": "No feasible itinerary found with given constraints"}))
        return

    # Build JSON itinerary in chronological order as ranges
    itinerary = []
    for city in found_order:
        s, e = found_ranges[city]
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
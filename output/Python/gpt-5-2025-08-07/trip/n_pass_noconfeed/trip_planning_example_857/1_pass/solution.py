import json
from itertools import permutations

def build_adjacency():
    edges = set()
    # Bidirectional edges ("and")
    pairs_bidirectional = [
        ("Hamburg", "Frankfurt"),
        ("Naples", "Mykonos"),
        ("Hamburg", "Porto"),
        ("Mykonos", "Geneva"),
        ("Frankfurt", "Geneva"),
        ("Frankfurt", "Porto"),
        ("Geneva", "Porto"),
        ("Geneva", "Manchester"),
        ("Naples", "Manchester"),
        ("Frankfurt", "Naples"),
        ("Frankfurt", "Manchester"),
        ("Naples", "Geneva"),
        ("Porto", "Manchester"),
        ("Hamburg", "Manchester"),
    ]
    for a, b in pairs_bidirectional:
        edges.add((a, b))
        edges.add((b, a))
    # Directed edge
    edges.add(("Hamburg", "Geneva"))  # from Hamburg to Geneva
    return edges

def compute_day_ranges(order, durations):
    # Build consecutive day ranges with overlap (flight day counts for both cities)
    ranges = {}
    start = 1
    for i, city in enumerate(order):
        if i == 0:
            start = 1
        else:
            start = ranges[order[i-1]][1]  # overlap on transition day
        end = start + durations[city] - 1
        ranges[city] = (start, end)
    return ranges

def days_set(start, end):
    return set(range(start, end + 1))

def is_connected(order, edges):
    for i in range(len(order) - 1):
        if (order[i], order[i+1]) not in edges:
            return False
    return True

def satisfies_constraints(order, durations, total_days, edges):
    # Connectivity
    if not is_connected(order, edges):
        return False, None

    # Compute ranges
    ranges = compute_day_ranges(order, durations)

    # Final day must be total_days
    if ranges[order[-1]][1] != total_days:
        return False, None

    # Must visit each city for exact required days (by construction) and check overlaps total
    # Validate total unique days equals total_days and sum of city-days equals total_days + (n-1)
    all_day_sets = []
    for city in order:
        s, e = ranges[city]
        all_day_sets.append(days_set(s, e))

    unique_days = set().union(*all_day_sets)
    if min(unique_days) != 1 or max(unique_days) != total_days or len(unique_days) != total_days:
        return False, None

    # Frankfurt days 5-6 exactly (duration 2)
    f_start, f_end = ranges["Frankfurt"]
    if not (f_start == 5 and f_end == 6):
        return False, None

    # Mykonos must include at least one day between 10 and 12 inclusive
    myk_s, myk_e = ranges["Mykonos"]
    if len(days_set(myk_s, myk_e).intersection(days_set(10, 12))) == 0:
        return False, None

    # Manchester must include at least one day between 15 and 18 inclusive
    man_s, man_e = ranges["Manchester"]
    if len(days_set(man_s, man_e).intersection(days_set(15, 18))) == 0:
        return False, None

    # Validate per-city duration match
    for city in durations:
        s, e = ranges[city]
        if (e - s + 1) != durations[city]:
            return False, None

    # Verify number of transitions equals len(order)-1 and sum of city-days = total_days + transitions
    transitions = len(order) - 1
    city_days_sum = sum(durations.values())
    if city_days_sum != total_days + transitions:
        return False, None

    return True, ranges

def main():
    # Input variables (constraints)
    total_days = 18
    cities = ["Porto", "Geneva", "Mykonos", "Manchester", "Hamburg", "Naples", "Frankfurt"]
    durations = {
        "Porto": 2,
        "Geneva": 3,
        "Mykonos": 3,
        "Manchester": 4,
        "Hamburg": 5,
        "Naples": 5,
        "Frankfurt": 2,
    }
    # Special timing constraints (embedded in validation):
    # - Frankfurt must be Day 5-6
    # - Mykonos must overlap Day 10-12 (inclusive)
    # - Manchester must overlap Day 15-18 (inclusive)

    edges = build_adjacency()

    # Optional pruning: Frankfurt must start Day 5 -> sum(dur-1 of preceding cities) == 4
    dur_minus_one = {c: durations[c] - 1 for c in cities if c != "Frankfurt"}

    def can_start_frankfurt_at_5(prefix):
        return sum(dur_minus_one[c] for c in prefix) == 4

    feasible_order = None
    feasible_ranges = None

    # To speed up search, enumerate permutations with Frankfurt positioned such that the
    # cumulative (dur-1) before it equals 4.
    for order in permutations(cities):
        # Quick prune on Frankfurt positioning
        idx_f = order.index("Frankfurt")
        prefix = order[:idx_f]
        if sum((durations[c] - 1) for c in prefix) != 4:
            continue

        ok, ranges = satisfies_constraints(order, durations, total_days, edges)
        if ok:
            feasible_order = order
            feasible_ranges = ranges
            break

    if not feasible_order:
        # In the unlikely case no feasible order is found, output an empty itinerary
        print(json.dumps({"itinerary": []}))
        return

    # Build itinerary output
    itinerary = []
    for city in feasible_order:
        s, e = feasible_ranges[city]
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
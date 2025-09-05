import itertools
import json

def build_directed_edges():
    # Define directed flight network based on the problem statement
    # "A and B" => bidirectional; "from A to B" => directed A->B
    cities = ["Reykjavik", "Istanbul", "Edinburgh", "Oslo", "Stuttgart", "Bucharest"]
    edges = set()
    def add_bidirectional(a, b):
        edges.add((a, b))
        edges.add((b, a))
    def add_directed(a, b):
        edges.add((a, b))

    add_bidirectional("Bucharest", "Oslo")
    add_bidirectional("Istanbul", "Oslo")
    add_directed("Reykjavik", "Stuttgart")  # one-way
    add_bidirectional("Bucharest", "Istanbul")
    add_bidirectional("Stuttgart", "Edinburgh")
    add_bidirectional("Istanbul", "Edinburgh")
    add_bidirectional("Oslo", "Reykjavik")
    add_bidirectional("Istanbul", "Stuttgart")
    add_bidirectional("Oslo", "Edinburgh")

    return cities, edges

def compute_day_ranges(order, durations):
    # Compute day ranges with one-day overlaps between consecutive cities
    # start day of first city is Day 1
    day_ranges = {}
    start_day = 1
    for i, city in enumerate(order):
        dur = durations[city]
        end_day = start_day + dur - 1
        day_ranges[city] = (start_day, end_day)
        # next city starts on the same day as current end (one-day overlap for flight day)
        start_day = end_day
    total_unique_days = day_ranges[order[-1]][1]
    return day_ranges, total_unique_days

def overlap_len(a1, a2, b1, b2):
    return max(0, min(a2, b2) - max(a1, b1) + 1)

def main():
    # Input variables (constraints)
    durations = {
        "Reykjavik": 5,
        "Istanbul": 4,
        "Edinburgh": 5,
        "Oslo": 2,
        "Stuttgart": 3,
        "Bucharest": 5
    }
    total_days_required = 19
    istanbul_window = (5, 8)  # inclusive
    oslo_window = (8, 9)      # inclusive

    cities, edges = build_directed_edges()

    # Validate sum and theoretical total days with N-1 overlaps
    S = sum(durations[c] for c in cities)
    n = len(cities)
    # With one-day overlaps between each consecutive city: unique_days = S - (n-1)
    assert S - (n - 1) == total_days_required, "Durations and overlaps do not match total_days."

    best = None  # (score_tuple, order, day_ranges)

    for order in itertools.permutations(cities):
        # Ensure consecutive cities are connected by a direct flight in the given direction
        feasible = True
        for i in range(n - 1):
            if (order[i], order[i + 1]) not in edges:
                feasible = False
                break
        if not feasible:
            continue

        # Compute day ranges
        day_ranges, total_unique_days = compute_day_ranges(order, durations)

        # Must exactly end on the total required days
        if total_unique_days != total_days_required:
            continue

        # Window constraints
        ist_start, ist_end = day_ranges["Istanbul"]
        osl_start, osl_end = day_ranges["Oslo"]
        ist_overlap = overlap_len(ist_start, ist_end, istanbul_window[0], istanbul_window[1])
        osl_overlap = overlap_len(osl_start, osl_end, oslo_window[0], oslo_window[1])

        # Feasibility: at least one day overlap in each respective window
        if ist_overlap < 1 or osl_overlap < 1:
            continue

        # Score: prefer more overlap in Oslo (ideally both day 8 and 9), then more in Istanbul
        # Tie-breakers: earlier Istanbul start, earlier Oslo start, lexicographic order
        score = (
            osl_overlap,             # maximize Oslo overlap
            ist_overlap,             # then maximize Istanbul overlap
            -ist_start,              # earlier Istanbul start (smaller ist_start)
            -osl_start,              # earlier Oslo start
            tuple(order)             # stable tie-breaker
        )

        if best is None or score > best[0]:
            best = (score, order, day_ranges)

    if best is None:
        # Fallback: no feasible solution (should not happen with given inputs)
        print(json.dumps({"itinerary": []}))
        return

    _, order, day_ranges = best

    # Build output itinerary as a list of day_range/place mappings
    itinerary = []
    for city in order:
        start, end = day_ranges[city]
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
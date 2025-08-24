import itertools
import json

def main():
    # Trip constraints (input variables)
    total_days = 15
    cities = ["Dublin", "Helsinki", "Riga", "Reykjavik", "Vienna", "Tallinn"]
    required_days = {
        "Dublin": 5,
        "Helsinki": 3,
        "Riga": 3,
        "Reykjavik": 2,
        "Vienna": 2,
        "Tallinn": 5,
    }
    # Event windows (inclusive, calendar days)
    vienna_show_window = (2, 3)        # Must be in Vienna on days 2 and 3
    helsinki_meet_window = (3, 5)      # Must be in Helsinki at least one day between 3 and 5
    tallinn_wedding_window = (7, 11)   # Must be in Tallinn at least one day between 7 and 11

    # Direct flights
    undirected_pairs = [
        ("Helsinki", "Riga"),
        ("Vienna", "Helsinki"),
        ("Riga", "Dublin"),
        ("Vienna", "Riga"),
        ("Reykjavik", "Vienna"),
        ("Helsinki", "Dublin"),
        ("Tallinn", "Dublin"),
        ("Reykjavik", "Helsinki"),
        ("Reykjavik", "Dublin"),
        ("Helsinki", "Tallinn"),
        ("Vienna", "Dublin"),
    ]
    directed_pairs = [
        ("Riga", "Tallinn"),  # one-way as specified
    ]

    # Build adjacency set for direct flights
    adjacency = set()
    for a, b in undirected_pairs:
        adjacency.add((a, b))
        adjacency.add((b, a))
    for a, b in directed_pairs:
        adjacency.add((a, b))

    # Helper functions
    def compute_ranges(order):
        """Compute day ranges with overlap-on-transition rule."""
        ranges = {}
        start = 1
        for city in order:
            length = required_days[city]
            end = start + length - 1
            ranges[city] = (start, end)
            start = end  # next segment starts at current end (overlap day)
        return ranges

    def valid_adjacency(order):
        """Check that each consecutive pair has a direct flight."""
        for i in range(1, len(order)):
            if (order[i-1], order[i]) not in adjacency:
                return False
        return True

    def intersects(a, b):
        """Whether two inclusive ranges (s,e) intersect."""
        return not (a[1] < b[0] or a[0] > b[1])

    def intersection_len(a, b):
        if not intersects(a, b):
            return 0
        return min(a[1], b[1]) - max(a[0], b[0]) + 1

    # Quick feasibility checks based on sums
    assert sum(required_days[c] for c in cities) == total_days + (len(cities) - 1), \
        "Sum of city-day requirements must equal total_days + (num_transitions)."

    best_solution = None
    best_score = None

    # Search all permutations for an optimal feasible itinerary
    for order in itertools.permutations(cities):
        if not valid_adjacency(order):
            continue

        ranges = compute_ranges(order)
        # Ensure total calendar span is exactly 1..total_days
        if ranges[order[-1]][1] != total_days or ranges[order[0]][0] != 1:
            continue

        # Vienna must be exactly days 2-3 (since length is 2 and must include 2 and 3)
        if ranges["Vienna"] != vienna_show_window:
            continue

        # Helsinki must intersect [3,5]
        if intersection_len(ranges["Helsinki"], helsinki_meet_window) == 0:
            continue

        # Tallinn must intersect [7,11]
        if intersection_len(ranges["Tallinn"], tallinn_wedding_window) == 0:
            continue

        # Score: maximize overlap with event windows (prefer full coverage when possible)
        hel_overlap = intersection_len(ranges["Helsinki"], helsinki_meet_window)
        tll_overlap = intersection_len(ranges["Tallinn"], tallinn_wedding_window)
        # Weight Tallinn window slightly higher due to wedding importance
        score = (tll_overlap * 100) + hel_overlap

        if best_score is None or score > best_score:
            best_score = score
            best_solution = (order, ranges)

    if best_solution is None:
        raise RuntimeError("No feasible itinerary found with given constraints.")

    order, ranges = best_solution

    # Build output itinerary
    itinerary = []
    for city in order:
        s, e = ranges[city]
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
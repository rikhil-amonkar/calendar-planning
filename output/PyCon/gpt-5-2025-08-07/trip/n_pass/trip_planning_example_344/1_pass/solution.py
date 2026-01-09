import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables (trip constraints)
    total_days = 20
    cities = ["Valencia", "Athens", "Naples", "Zurich"]
    required_days = {
        "Valencia": 6,
        "Athens": 6,
        "Naples": 5,
        "Zurich": 6,
    }
    # Windows where presence must occur (inclusive)
    must_be_in_window = {
        "Athens": (1, 6),   # visit relatives in Athens between day 1 and day 6
        "Naples": (16, 20)  # attend a wedding in Naples between day 16 and day 20
    }
    # Direct flight network (directed where specified)
    edges = set()
    def add_ud(a, b):
        edges.add((a, b))
        edges.add((b, a))
    add_ud("Valencia", "Naples")
    edges.add(("Valencia", "Athens"))  # directed: from Valencia to Athens
    add_ud("Athens", "Naples")
    add_ud("Zurich", "Naples")
    add_ud("Athens", "Zurich")
    add_ud("Zurich", "Valencia")

    # CSP setup
    problem = Problem()
    problem.addVariable("f1", range(1, total_days + 1))
    problem.addVariable("f2", range(1, total_days + 1))
    problem.addVariable("f3", range(1, total_days + 1))
    problem.addVariable("C1", cities)
    problem.addVariable("C2", cities)
    problem.addVariable("C3", cities)
    problem.addVariable("C4", cities)
    problem.addConstraint(AllDifferentConstraint(), ["C1", "C2", "C3", "C4"])

    def itinerary_constraint(f1, f2, f3, C1, C2, C3, C4):
        # flight days strictly increasing
        if not (1 <= f1 < f2 < f3 <= total_days):
            return False

        # Segment day ranges (inclusive), flight day counts for both segments
        starts = [1, f1, f2, f3]
        ends = [f1, f2, f3, total_days]

        # Segment lengths
        L1 = ends[0] - starts[0] + 1  # f1 - 1 + 1 = f1
        L2 = ends[1] - starts[1] + 1  # f2 - f1 + 1
        L3 = ends[2] - starts[2] + 1  # f3 - f2 + 1
        L4 = ends[3] - starts[3] + 1  # total_days - f3 + 1
        if L1 <= 0 or L2 <= 0 or L3 <= 0 or L4 <= 0:
            return False

        # Required durations per city
        seg_cities = [C1, C2, C3, C4]
        seg_lengths = [L1, L2, L3, L4]
        for city, length in zip(seg_cities, seg_lengths):
            if required_days[city] != length:
                return False

        # Direct flights between consecutive cities
        if (C1, C2) not in edges or (C2, C3) not in edges or (C3, C4) not in edges:
            return False

        # Window constraints: ensure overlap with specified windows
        # Overlap condition: max(seg_start, win_start) <= min(seg_end, win_end)
        def overlaps(a_start, a_end, b_start, b_end):
            return max(a_start, b_start) <= min(a_end, b_end)

        # Athens window
        awin = must_be_in_window["Athens"]
        if not any(seg_cities[i] == "Athens" and overlaps(starts[i], ends[i], awin[0], awin[1]) for i in range(4)):
            return False

        # Naples window
        nwin = must_be_in_window["Naples"]
        if not any(seg_cities[i] == "Naples" and overlaps(starts[i], ends[i], nwin[0], nwin[1]) for i in range(4)):
            return False

        # Sum check: sum of segment lengths equals total days + number of flights (3)
        if sum(seg_lengths) != total_days + 3:
            return False

        return True

    problem.addConstraint(
        itinerary_constraint,
        ["f1", "f2", "f3", "C1", "C2", "C3", "C4"]
    )

    # Find solutions and pick an optimal one (earliest flights, then lexicographically smallest city tuple)
    solutions = problem.getSolutions()
    if not solutions:
        print(json.dumps({"itinerary": []}))
        return

    def sol_key(sol):
        return (
            sol["f1"],
            sol["f2"],
            sol["f3"],
            (sol["C1"], sol["C2"], sol["C3"], sol["C4"]),
        )

    best = min(solutions, key=sol_key)

    # Build itinerary
    f1, f2, f3 = best["f1"], best["f2"], best["f3"]
    C1, C2, C3, C4 = best["C1"], best["C2"], best["C3"], best["C4"]

    segments = [
        (1, f1, C1),
        (f1, f2, C2),
        (f2, f3, C3),
        (f3, total_days, C4),
    ]

    output = {
        "itinerary": [
            {"day_range": f"Day {start}-{end}", "place": place}
            for (start, end, place) in segments
        ]
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()
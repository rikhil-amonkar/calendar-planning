import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Cities and required durations
    cities = ["Amsterdam", "Edinburgh", "Brussels", "Vienna", "Berlin", "Reykjavik"]
    durations = {
        "Amsterdam": 4,
        "Edinburgh": 5,
        "Brussels": 5,
        "Vienna": 5,
        "Berlin": 4,
        "Reykjavik": 5,
    }

    # Direct flight connections (undirected)
    direct_pairs = {
        ("Edinburgh", "Berlin"),
        ("Amsterdam", "Berlin"),
        ("Edinburgh", "Amsterdam"),
        ("Vienna", "Berlin"),
        ("Berlin", "Brussels"),
        ("Vienna", "Reykjavik"),
        ("Edinburgh", "Brussels"),
        ("Vienna", "Brussels"),
        ("Amsterdam", "Vienna"),
        ("Amsterdam", "Reykjavik"),
        ("Reykjavik", "Brussels"),
        ("Reykjavik", "Berlin"),
    }
    direct_edges = {frozenset(p) for p in direct_pairs}

    # Create CSP
    problem = Problem()

    # Position variables for a 6-city itinerary (with 1-day overlaps on travel days)
    pos_vars = [f"pos{i}" for i in range(1, 7)]
    for v in pos_vars:
        problem.addVariable(v, cities)

    # All cities must be used exactly once
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Adjacent positions must have a direct flight
    for i in range(1, 6):
        problem.addConstraint(
            lambda a, b, edges=direct_edges: frozenset((a, b)) in edges,
            (f"pos{i}", f"pos{i+1}")
        )

    # Custom constraint to enforce day windows and durations with overlap rule:
    # Start days are computed as:
    # - start of first city = Day 1
    # - start of next city = end day of previous city (overlap on travel day)
    # End day = start + duration - 1
    # Fixed requirements:
    # - Amsterdam must cover Day 5-8 (length 4) => start 5
    # - Reykjavik must cover Day 12-16 (length 5) => start 12
    # - Berlin must cover Day 16-19 (length 4) => start 16
    def window_constraint(*assigned):
        seq = list(assigned)  # order is pos1..pos6
        # Compute starts and ends
        start_day = 1
        starts = {}
        ends = {}
        for city in seq:
            starts[city] = start_day
            ends[city] = start_day + durations[city] - 1
            start_day = ends[city]  # next city starts on same day as this city ends

        # Enforce exact windows
        if starts.get("Amsterdam") != 5 or ends.get("Amsterdam") != 8:
            return False
        if starts.get("Reykjavik") != 12 or ends.get("Reykjavik") != 16:
            return False
        if starts.get("Berlin") != 16 or ends.get("Berlin") != 19:
            return False

        # Ensure complete trip spans exactly Day 1 to Day 23
        # Last city's end should be 23
        if list(ends[seq[-1]] for _ in [0])[0] != 23:
            return False

        return True

    problem.addConstraint(window_constraint, tuple(pos_vars))

    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"itinerary": []}))
        return

    # Build itinerary in order
    ordered_cities = [solution[f"pos{i}"] for i in range(1, 7)]
    itinerary = []
    start_day = 1
    for city in ordered_cities:
        end_day = start_day + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })
        start_day = end_day  # next city starts on the same day (overlap travel day)

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
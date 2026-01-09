import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables (trip constraints)
    total_days = 14
    cities = ["Amsterdam", "Vienna", "Santorini", "Lyon"]
    desired_days = {
        "Amsterdam": 3,
        "Vienna": 7,
        "Santorini": 4,
        "Lyon": 3
    }
    # Must attend in these windows (inclusive)
    city_windows = {
        "Amsterdam": (9, 11),  # workshop between day 9 and 11
        "Lyon": (7, 9)         # wedding between day 7 and 9
    }
    # Direct flights (undirected)
    direct_pairs = {
        frozenset(["Vienna", "Lyon"]),
        frozenset(["Vienna", "Santorini"]),
        frozenset(["Vienna", "Amsterdam"]),
        frozenset(["Amsterdam", "Santorini"]),
        frozenset(["Lyon", "Amsterdam"])
    }

    # Create CSP
    problem = Problem()

    blocks = [1, 2, 3, 4]  # four city blocks in order

    # Variables
    for i in blocks:
        problem.addVariable(f"C{i}", cities)  # city in block i
        problem.addVariable(f"S{i}", range(1, total_days + 1))  # start day of block i
        problem.addVariable(f"E{i}", range(1, total_days + 1))  # end day of block i

    # All cities must be distinct (exactly these 4)
    problem.addConstraint(AllDifferentConstraint(), [f"C{i}" for i in blocks])

    # Start on day 1, end on day 14 (cover the full 14-day trip)
    problem.addConstraint(lambda s: s == 1, ("S1",))
    problem.addConstraint(lambda e: e == total_days, ("E4",))

    # Each block has non-negative duration and proper order
    for i in blocks:
        problem.addConstraint(lambda s, e: s <= e, (f"S{i}", f"E{i}"))

    # Transitions: end of block i is the same calendar day as start of block i+1
    # This models a flight day that counts for both cities.
    problem.addConstraint(lambda e1, s2: e1 == s2, ("E1", "S2"))
    problem.addConstraint(lambda e2, s3: e2 == s3, ("E2", "S3"))
    problem.addConstraint(lambda e3, s4: e3 == s4, ("E3", "S4"))

    # Durations per city block must match desired city-day counts
    for i in blocks:
        problem.addConstraint(
            lambda c, s, e, dd=desired_days: (e - s + 1) == dd[c],
            (f"C{i}", f"S{i}", f"E{i}")
        )

    # Direct flight constraint between consecutive city blocks
    problem.addConstraint(
        lambda c1, c2, dp=direct_pairs: frozenset([c1, c2]) in dp,
        ("C1", "C2")
    )
    problem.addConstraint(
        lambda c2, c3, dp=direct_pairs: frozenset([c2, c3]) in dp,
        ("C2", "C3")
    )
    problem.addConstraint(
        lambda c3, c4, dp=direct_pairs: frozenset([c3, c4]) in dp,
        ("C3", "C4")
    )

    # City window constraints (must be in city during specified windows)
    def window_constraint(city, s, e, windows):
        if city in windows:
            low, high = windows[city]
            return not (e < low or s > high)
        return True

    for i in blocks:
        problem.addConstraint(
            lambda c, s, e, w=city_windows: window_constraint(c, s, e, w),
            (f"C{i}", f"S{i}", f"E{i}")
        )

    # Solve
    solutions = problem.getSolutions()

    if not solutions:
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    # Choose a deterministic solution (sort by time and city names)
    def sol_key(sol):
        return (
            sol["S1"], sol["E1"],
            sol["S2"], sol["E2"],
            sol["S3"], sol["E3"],
            sol["S4"], sol["E4"],
            sol["C1"], sol["C2"], sol["C3"], sol["C4"]
        )

    sol = sorted(solutions, key=sol_key)[0]

    itinerary = []
    for i in blocks:
        itinerary.append({
            "day_range": f"Day {sol[f'S{i}']}-{sol[f'E{i}']}",
            "place": sol[f"C{i}"]
        })

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()
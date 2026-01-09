import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables and constraints
    total_days = 15
    cities = ["Manchester", "Madrid", "Vienna", "Stuttgart"]
    durations = {
        "Manchester": 7,
        "Stuttgart": 5,
        "Madrid": 4,
        "Vienna": 2,
    }
    # Required continuous presence windows (inclusive)
    required_windows = {
        "Manchester": (1, 7),
        "Stuttgart": (11, 15),
    }
    # Direct flight pairs (undirected)
    direct_flights = {
        frozenset(("Vienna", "Stuttgart")),
        frozenset(("Manchester", "Vienna")),
        frozenset(("Madrid", "Vienna")),
        frozenset(("Manchester", "Stuttgart")),
        frozenset(("Manchester", "Madrid")),
    }

    # Create CSP
    problem = Problem()

    # Segment variables
    segments = [1, 2, 3, 4]
    C_vars = [f"C{i}" for i in segments]
    S_vars = [f"S{i}" for i in segments]
    E_vars = [f"E{i}" for i in segments]

    # City domain per segment:
    # First segment must be Manchester due to (1..7) window; last must be Stuttgart due to (11..15) window.
    problem.addVariable("C1", ["Manchester"])
    problem.addVariable("C4", ["Stuttgart"])
    # Middle two segments are the remaining two cities
    problem.addVariable("C2", ["Madrid", "Vienna"])
    problem.addVariable("C3", ["Madrid", "Vienna"])
    problem.addConstraint(AllDifferentConstraint(), ("C1", "C2", "C3", "C4"))

    # Day domains
    problem.addVariable("S1", [1])   # Trip starts Day 1
    problem.addVariable("E4", [total_days])  # Trip ends Day 15
    for i in [2, 3, 4]:
        problem.addVariable(f"S{i}", range(1, total_days + 1))
    for i in [1, 2, 3]:
        problem.addVariable(f"E{i}", range(1, total_days + 1))

    # Structural constraints: S_i <= E_i and overlaps on transition days (flight days)
    for i in segments:
        problem.addConstraint(lambda s, e: s <= e, (f"S{i}", f"E{i}"))

    # Overlap (flight) on transition days: next start equals previous end
    problem.addConstraint(lambda e1, s2: e1 == s2, ("E1", "S2"))
    problem.addConstraint(lambda e2, s3: e2 == s3, ("E2", "S3"))
    problem.addConstraint(lambda e3, s4: e3 == s4, ("E3", "S4"))

    # Durations per city segment: Ei - Si + 1 == duration(city)
    for i in segments:
        def duration_ok(city, s, e, durs=durations):
            return (e - s + 1) == durs[city]
        problem.addConstraint(duration_ok, (f"C{i}", f"S{i}", f"E{i}"))

    # Required presence windows:
    # If a city has a required window (a..b), ensure its segment covers that range.
    for i in segments:
        def window_ok(city, s, e, windows=required_windows):
            if city in windows:
                a, b = windows[city]
                return s <= a and e >= b
            return True
        problem.addConstraint(window_ok, (f"C{i}", f"S{i}", f"E{i}"))

    # Direct flight adjacency between consecutive segments
    def is_direct(a, b, edges=direct_flights):
        return frozenset((a, b)) in edges

    problem.addConstraint(is_direct, ("C1", "C2"))
    problem.addConstraint(is_direct, ("C2", "C3"))
    problem.addConstraint(is_direct, ("C3", "C4"))

    # Solve
    solution = problem.getSolution()

    itinerary = []
    if solution:
        # Build itinerary as ordered segments 1..4
        for i in segments:
            s = solution[f"S{i}"]
            e = solution[f"E{i}"]
            c = solution[f"C{i}"]
            itinerary.append({
                "day_range": f"Day {s}-{e}",
                "place": c
            })

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
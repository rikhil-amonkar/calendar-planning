import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input parameters
    total_days = 16
    cities = ["Istanbul", "Rome", "Seville", "Naples", "Santorini"]
    durations = {
        "Istanbul": 2,
        "Rome": 3,
        "Seville": 4,
        "Naples": 7,
        "Santorini": 4,
    }

    # Special window constraints
    istanbul_window = (6, 7)   # Must be in Istanbul on days 6-7 (inclusive)
    santorini_window = (13, 16)  # Must be in Santorini on days 13-16 (inclusive)

    # Allowed direct flights (undirected)
    direct_pairs = [
        ("Rome", "Santorini"),
        ("Seville", "Rome"),
        ("Istanbul", "Naples"),
        ("Naples", "Santorini"),
        ("Rome", "Naples"),
        ("Rome", "Istanbul"),
    ]
    direct_set = set(frozenset(pair) for pair in direct_pairs)

    # Helper constraint: adjacency must be a direct flight
    def is_direct(a, b):
        return frozenset([a, b]) in direct_set

    # Chain constraint for durations and overlapping travel day rule
    def chain_constraint(p1, p2, p3, p4, p5, e1, e2, e3, e4, e5):
        # End days must follow: 
        # e1 = dur(p1)
        # e2 = e1 + dur(p2) - 1
        # e3 = e2 + dur(p3) - 1
        # e4 = e3 + dur(p4) - 1
        # e5 = e4 + dur(p5) - 1 = total_days
        try:
            if e1 != durations[p1]:
                return False
            if e2 != e1 + durations[p2] - 1:
                return False
            if e3 != e2 + durations[p3] - 1:
                return False
            if e4 != e3 + durations[p4] - 1:
                return False
            if e5 != e4 + durations[p5] - 1:
                return False
            if e5 != total_days:
                return False
        except KeyError:
            return False
        # Monotonic non-decreasing ends within valid range
        if not (1 <= e1 <= e2 <= e3 <= e4 <= e5 <= total_days):
            return False
        return True

    # Window constraint for a specific city
    def city_window_constraint(p1, p2, p3, p4, p5, e1, e2, e3, e4, e5, city, start_target, end_target):
        ps = [p1, p2, p3, p4, p5]
        ends = [e1, e2, e3, e4, e5]
        if city not in ps:
            return False
        idx = ps.index(city)
        start = 1 if idx == 0 else ends[idx - 1]
        end = ends[idx]
        return start == start_target and end == end_target

    # Build CSP
    problem = Problem()
    # City order variables
    for i in range(1, 6):
        problem.addVariable(f"P{i}", cities)
    problem.addConstraint(AllDifferentConstraint(), [f"P{i}" for i in range(1, 6)])

    # End days for each segment
    for i in range(1, 6):
        problem.addVariable(f"E{i}", list(range(1, total_days + 1)))

    # Adjacency constraints (direct flights between consecutive cities)
    problem.addConstraint(lambda a, b, f=is_direct: f(a, b), ("P1", "P2"))
    problem.addConstraint(lambda a, b, f=is_direct: f(a, b), ("P2", "P3"))
    problem.addConstraint(lambda a, b, f=is_direct: f(a, b), ("P3", "P4"))
    problem.addConstraint(lambda a, b, f=is_direct: f(a, b), ("P4", "P5"))

    # Chain constraint for durations and total days
    problem.addConstraint(
        chain_constraint,
        ("P1", "P2", "P3", "P4", "P5", "E1", "E2", "E3", "E4", "E5"),
    )

    # City window constraints
    problem.addConstraint(
        lambda p1, p2, p3, p4, p5, e1, e2, e3, e4, e5, ct=city_window_constraint, s=istanbul_window[0], t=istanbul_window[1]:
            ct(p1, p2, p3, p4, p5, e1, e2, e3, e4, e5, "Istanbul", s, t),
        ("P1", "P2", "P3", "P4", "P5", "E1", "E2", "E3", "E4", "E5"),
    )

    problem.addConstraint(
        lambda p1, p2, p3, p4, p5, e1, e2, e3, e4, e5, ct=city_window_constraint, s=santorini_window[0], t=santorini_window[1]:
            ct(p1, p2, p3, p4, p5, e1, e2, e3, e4, e5, "Santorini", s, t),
        ("P1", "P2", "P3", "P4", "P5", "E1", "E2", "E3", "E4", "E5"),
    )

    # Solve
    solutions = problem.getSolutions()

    itinerary_output = {"itinerary": []}
    if solutions:
        # Choose a deterministic solution (sort by tuple of P1..P5 then E1..E5)
        def sol_key(sol):
            return (sol["P1"], sol["P2"], sol["P3"], sol["P4"], sol["P5"],
                    sol["E1"], sol["E2"], sol["E3"], sol["E4"], sol["E5"])
        solution = sorted(solutions, key=sol_key)[0]

        segments = []
        for i in range(1, 6):
            place = solution[f"P{i}"]
            start_day = 1 if i == 1 else solution[f"E{i-1}"]
            end_day = solution[f"E{i}"]
            segments.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": place
            })

        itinerary_output["itinerary"] = segments

    print(json.dumps(itinerary_output, ensure_ascii=False))

if __name__ == "__main__":
    main()
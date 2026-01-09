import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables (trip constraints)
    total_days = 12
    cities = ["Prague", "Berlin", "Tallinn", "Stockholm"]

    required_days = {
        "Prague": 2,
        "Berlin": 3,
        "Tallinn": 5,
        "Stockholm": 5,
    }

    # Undirected direct flight edges as frozensets
    direct_flights = {
        frozenset(("Berlin", "Tallinn")),
        frozenset(("Prague", "Tallinn")),
        frozenset(("Stockholm", "Tallinn")),
        frozenset(("Prague", "Stockholm")),
        frozenset(("Stockholm", "Berlin")),
    }

    # Helper to compute segments (city, start_day, end_day) from order
    def compute_segments(order):
        L0 = required_days[order[0]]
        L1 = required_days[order[1]]
        L2 = required_days[order[2]]
        # L3 implied by totals and overlaps
        # Boundaries (shared days between consecutive cities)
        d1 = L0
        d2 = L0 + L1 - 1
        d3 = L0 + L1 + L2 - 2

        segments = [
            (order[0], 1, d1),
            (order[1], d1, d2),
            (order[2], d2, d3),
            (order[3], d3, total_days),
        ]
        return segments

    # Build the constraint problem
    problem = Problem()
    order_vars = ["order0", "order1", "order2", "order3"]
    for v in order_vars:
        problem.addVariable(v, cities)
    problem.addConstraint(AllDifferentConstraint(), order_vars)

    # Constraint: adjacency must be connected by direct flights
    def adjacency_constraint(o0, o1, o2, o3):
        return (frozenset((o0, o1)) in direct_flights and
                frozenset((o1, o2)) in direct_flights and
                frozenset((o2, o3)) in direct_flights)

    problem.addConstraint(adjacency_constraint, order_vars)

    # Constraint: Berlin on day 6 and day 8; Tallinn covers days 8-12 inclusive
    def day_constraints(o0, o1, o2, o3):
        order = [o0, o1, o2, o3]
        # Compute segments and coverage
        segments = compute_segments(order)
        coverage = {city: (start, end) for city, start, end in segments}

        # Validate boundaries monotonicity (implicitly true with positive lengths)
        starts_ends = [coverage[o0], coverage[o1], coverage[o2], coverage[o3]]
        if not (1 <= starts_ends[0][0] <= starts_ends[0][1] <=
                starts_ends[1][1] <= starts_ends[2][1] <= starts_ends[3][1] == total_days):
            return False

        # Berlin must include day 6 and day 8
        b_start, b_end = coverage["Berlin"]
        if not (b_start <= 6 <= b_end and b_start <= 8 <= b_end):
            return False

        # Tallinn must be exactly days 8-12
        t_start, t_end = coverage["Tallinn"]
        if not (t_start == 8 and t_end == 12):
            return False

        # Ensure each city's segment length equals required days
        for city, (s, e) in coverage.items():
            if (e - s + 1) != required_days[city]:
                return False

        return True

    problem.addConstraint(day_constraints, order_vars)

    solutions = problem.getSolutions()

    if not solutions:
        print(json.dumps({"itinerary": []}, ensure_ascii=False))
        return

    # Choose the first valid solution
    sol = solutions[0]
    order = [sol["order0"], sol["order1"], sol["order2"], sol["order3"]]
    segments = compute_segments(order)

    # Build JSON itinerary
    itinerary = []
    for city, start, end in segments:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables (constraints)
    total_days = 17
    cities = ["Naples", "Vienna", "Vilnius"]
    required_days = {"Naples": 5, "Vienna": 7, "Vilnius": 7}
    # Direct flights (treat as undirected edges)
    direct_flights = {frozenset(["Naples", "Vienna"]), frozenset(["Vienna", "Vilnius"])}

    # Set up CSP
    problem = Problem()
    problem.addVariables(["City1", "City2", "City3"], cities)
    problem.addConstraint(AllDifferentConstraint(), ["City1", "City2", "City3"])

    # Only direct flights for consecutive moves
    problem.addConstraint(lambda a, b, edges=direct_flights: frozenset([a, b]) in edges, ("City1", "City2"))
    problem.addConstraint(lambda b, c, edges=direct_flights: frozenset([b, c]) in edges, ("City2", "City3"))

    # Travel day variables (inclusive overlap days)
    problem.addVariable("T1", range(1, total_days + 1))  # travel from City1 -> City2 on day T1
    problem.addVariable("T2", range(1, total_days + 1))  # travel from City2 -> City3 on day T2

    # Order of cities must satisfy relatives-in-Naples between day 1 and 5
    problem.addConstraint(lambda c1: c1 == "Naples", ("City1",))
    # Travel order constraints
    problem.addConstraint(lambda t1, t2: 1 <= t1 < t2 <= total_days, ("T1", "T2"))

    # Duration constraints derived from overlapping travel-day rule:
    # City1 occupies days 1..T1
    problem.addConstraint(lambda c1, t1, req=required_days: t1 == req[c1], ("City1", "T1"))
    # City2 occupies days T1..T2
    problem.addConstraint(lambda c2, t1, t2, req=required_days: (t2 - t1 + 1) == req[c2], ("City2", "T1", "T2"))
    # City3 occupies days T2..total_days
    problem.addConstraint(lambda c3, t2, total=total_days, req=required_days: (total - t2 + 1) == req[c3], ("City3", "T2"))

    # Solve
    solutions = problem.getSolutions()

    if not solutions:
        output = {"itinerary": []}
    else:
        # Choose the lexicographically smallest by (T1, T2) to be deterministic
        solutions.sort(key=lambda s: (s["T1"], s["T2"], s["City1"], s["City2"], s["City3"]))
        s = solutions[0]
        t1, t2 = s["T1"], s["T2"]
        itinerary = [
            {"day_range": f"Day 1-{t1}", "place": s["City1"]},
            {"day_range": f"Day {t1}-{t2}", "place": s["City2"]},
            {"day_range": f"Day {t2}-{total_days}", "place": s["City3"]},
        ]
        output = {"itinerary": itinerary}

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()
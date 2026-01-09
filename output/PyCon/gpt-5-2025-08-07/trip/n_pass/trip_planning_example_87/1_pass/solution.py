import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables (trip constraints)
    days_total = 7
    cities = ["Riga", "Amsterdam", "Mykonos"]
    target_days = {"Riga": 2, "Amsterdam": 2, "Mykonos": 5}
    direct_pairs = {("Amsterdam", "Mykonos"), ("Riga", "Amsterdam")}
    direct_edges = {frozenset(p) for p in direct_pairs}

    # Set up CSP
    problem = Problem()
    problem.addVariables(["C1", "C2", "C3"], cities)
    problem.addVariables(["f1", "f2"], range(1, days_total + 1))

    # Constraints
    # 1) Three distinct cities
    problem.addConstraint(AllDifferentConstraint(), ["C1", "C2", "C3"])

    # 2) Exactly the three specified cities are visited
    def exact_city_set(c1, c2, c3):
        return set([c1, c2, c3]) == set(cities)
    problem.addConstraint(exact_city_set, ["C1", "C2", "C3"])

    # 3) Flights occur on increasing days
    problem.addConstraint(lambda f1, f2: f1 < f2, ["f1", "f2"])

    # 4) Only direct flights between consecutive city segments
    def direct_conn(c1, c2, c3):
        return (frozenset([c1, c2]) in direct_edges) and (frozenset([c2, c3]) in direct_edges)
    problem.addConstraint(direct_conn, ["C1", "C2", "C3"])

    # 5) Visiting relatives in Riga between day 1 and day 2:
    #    Must be in Riga on both Day 1 and Day 2, which means C1 is Riga and f1 >= 2
    problem.addConstraint(lambda c1, f1: c1 == "Riga" and f1 >= 2, ["C1", "f1"])

    # 6) Duration targets with flight-day double counting handled by block model:
    #    Days: [1..f1]=C1, [f1..f2]=C2, [f2..days_total]=C3
    def durations_ok(c1, c2, c3, f1, f2):
        d1 = f1
        d2 = f2 - f1 + 1
        d3 = (days_total - f2 + 1)
        actual = {c1: d1, c2: d2, c3: d3}
        return (
            actual.get("Riga", 0) == target_days["Riga"] and
            actual.get("Amsterdam", 0) == target_days["Amsterdam"] and
            actual.get("Mykonos", 0) == target_days["Mykonos"]
        )
    problem.addConstraint(durations_ok, ["C1", "C2", "C3", "f1", "f2"])

    # Solve and pick an optimal solution (earliest possible first flight day, then second)
    solutions = problem.getSolutions()
    chosen = None
    if solutions:
        solutions.sort(key=lambda s: (s["f1"], s["f2"]))
        chosen = solutions[0]

    itinerary = []
    if chosen:
        f1, f2 = chosen["f1"], chosen["f2"]
        c1, c2, c3 = chosen["C1"], chosen["C2"], chosen["C3"]
        itinerary = [
            {"day_range": f"Day 1-{f1}", "place": c1},
            {"day_range": f"Day {f1}-{f2}", "place": c2},
            {"day_range": f"Day {f2}-{days_total}", "place": c3},
        ]

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
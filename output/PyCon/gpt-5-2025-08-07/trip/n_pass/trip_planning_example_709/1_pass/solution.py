import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Trip parameters
    total_days = 18
    cities = ["Helsinki", "Valencia", "Dubrovnik", "Porto", "Prague", "Reykjavik"]
    durations = {
        "Helsinki": 4,
        "Valencia": 5,
        "Dubrovnik": 4,
        "Porto": 3,
        "Prague": 3,
        "Reykjavik": 4,
    }

    # Direct flights (undirected)
    direct_flights = {
        frozenset(["Helsinki", "Prague"]),
        frozenset(["Prague", "Valencia"]),
        frozenset(["Valencia", "Porto"]),
        frozenset(["Helsinki", "Reykjavik"]),
        frozenset(["Dubrovnik", "Helsinki"]),
        frozenset(["Reykjavik", "Prague"]),
    }

    def has_direct(a, b):
        return frozenset([a, b]) in direct_flights

    # CSP setup
    problem = Problem()

    # Variables for city order (positions 1..6)
    pos_vars = [f"pos{i}" for i in range(1, 7)]
    for v in pos_vars:
        problem.addVariable(v, cities)
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Variables for start and end days for each position
    s_vars = [f"s{i}" for i in range(1, 7)]
    e_vars = [f"e{i}" for i in range(1, 7)]
    for v in s_vars + e_vars:
        problem.addVariable(v, range(1, total_days + 1))

    # Start at day 1
    problem.addConstraint(lambda s1: s1 == 1, ("s1",))

    # Duration consistency: e_i = s_i + duration(city_i) - 1
    for i in range(1, 7):
        problem.addConstraint(
            lambda city, s, e, d=durations: e == s + d[city] - 1,
            (f"pos{i}", f"s{i}", f"e{i}")
        )

    # Overlap on flight days: s_{i+1} = e_i (flight day counted in both cities)
    for i in range(1, 6):
        problem.addConstraint(lambda e_i, s_next: s_next == e_i, (f"e{i}", f"s{i+1}"))

    # Ensure the overall trip ends on day total_days
    problem.addConstraint(lambda e6: e6 == total_days, ("e6",))

    # Enforce direct flights between consecutive cities
    for i in range(1, 6):
        problem.addConstraint(
            lambda c1, c2, has_direct=has_direct: has_direct(c1, c2),
            (f"pos{i}", f"pos{i+1}")
        )

    # Porto meeting between day 16 and day 18: Porto segment must intersect [16,18]
    # Equivalent: if city == Porto then e >= 16 and s <= 18
    for i in range(1, 7):
        problem.addConstraint(
            lambda city, s, e: True if city != "Porto" else (e >= 16 and s <= 18),
            (f"pos{i}", f"s{i}", f"e{i}")
        )

    # Solve
    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"itinerary": [], "note": "No feasible itinerary found"}))
        return

    # Build itinerary in order
    itinerary = []
    for i in range(1, 7):
        s = solution[f"s{i}"]
        e = solution[f"e{i}"]
        city = solution[f"pos{i}"]
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
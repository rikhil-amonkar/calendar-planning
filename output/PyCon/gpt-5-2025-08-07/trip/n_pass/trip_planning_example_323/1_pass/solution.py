import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables (trip constraints)
    total_days = 16
    cities = ["London", "Split", "Oslo", "Porto"]
    durations = {
        "London": 7,
        "Split": 5,
        "Oslo": 2,
        "Porto": 5
    }
    # Direct flights (bidirectional)
    direct_flights = {
        ("London", "Oslo"), ("Oslo", "London"),
        ("Split", "Oslo"), ("Oslo", "Split"),
        ("Oslo", "Porto"), ("Porto", "Oslo"),
        ("London", "Split"), ("Split", "London")
    }

    # Annual show days in Split: Day 7 - Day 11 (inclusive)
    split_show_start, split_show_end = 7, 11
    # London relatives window: Day 1 - Day 7 (inclusive)
    london_relatives_start, london_relatives_end = 1, 7

    # Create constraint problem
    problem = Problem()

    # Variables for the ordered 4-city itinerary
    city_vars = ["c1", "c2", "c3", "c4"]
    start_vars = ["s1", "s2", "s3", "s4"]
    end_vars = ["e1", "e2", "e3", "e4"]

    # Domains
    for cv in city_vars:
        problem.addVariable(cv, cities)
    for sv in start_vars + end_vars:
        problem.addVariable(sv, range(1, total_days + 1))

    # All cities are distinct (visit 4 unique cities)
    problem.addConstraint(AllDifferentConstraint(), city_vars)

    # London fixed to be the first city and must be Day 1-7
    problem.addConstraint(lambda c: c == "London", ["c1"])
    problem.addConstraint(lambda s: s == london_relatives_start, ["s1"])
    problem.addConstraint(lambda e: e == london_relatives_end, ["e1"])

    # Split must cover the show days Day 7-11
    problem.addConstraint(lambda c: c == "Split", ["c2"])
    problem.addConstraint(lambda s: s == split_show_start, ["s2"])
    problem.addConstraint(lambda e: e == split_show_end, ["e2"])

    # Length constraints: e - s + 1 == durations[city]
    def length_constraint(city, s, e):
        return (e - s + 1) == durations[city]

    problem.addConstraint(length_constraint, ["c1", "s1", "e1"])
    problem.addConstraint(length_constraint, ["c2", "s2", "e2"])
    problem.addConstraint(length_constraint, ["c3", "s3", "e3"])
    problem.addConstraint(length_constraint, ["c4", "s4", "e4"])

    # Overlap one day on flight days (being in both cities that day)
    problem.addConstraint(lambda e1, s2: s2 == e1, ["e1", "s2"])
    problem.addConstraint(lambda e2, s3: s3 == e2, ["e2", "s3"])
    problem.addConstraint(lambda e3, s4: s4 == e3, ["e3", "s4"])

    # Total trip ends on Day 16
    problem.addConstraint(lambda e4: e4 == total_days, ["e4"])

    # Direct flight constraints between consecutive cities
    def flight_ok(a, b):
        return (a, b) in direct_flights

    problem.addConstraint(flight_ok, ["c1", "c2"])
    problem.addConstraint(flight_ok, ["c2", "c3"])
    problem.addConstraint(flight_ok, ["c3", "c4"])

    # Solve
    solution = problem.getSolution()

    # Build itinerary output
    itinerary = [
        {"day_range": f"Day {solution['s1']}-{solution['e1']}", "place": solution["c1"]},
        {"day_range": f"Day {solution['s2']}-{solution['e2']}", "place": solution["c2"]},
        {"day_range": f"Day {solution['s3']}-{solution['e3']}", "place": solution["c3"]},
        {"day_range": f"Day {solution['s4']}-{solution['e4']}", "place": solution["c4"]},
    ]

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
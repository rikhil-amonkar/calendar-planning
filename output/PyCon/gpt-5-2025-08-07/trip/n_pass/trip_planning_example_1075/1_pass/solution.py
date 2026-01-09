import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Cities and durations (days in each city)
    cities = ["Vienna", "Lyon", "Edinburgh", "Reykjavik", "Stuttgart", "Manchester", "Split", "Prague"]
    durations = {
        "Vienna": 4,
        "Lyon": 3,
        "Edinburgh": 4,
        "Reykjavik": 5,
        "Stuttgart": 5,
        "Manchester": 2,
        "Split": 5,
        "Prague": 4,
    }

    total_days = 25  # Total calendar days

    # Direct flight connections (undirected)
    direct_pairs = [
        ("Reykjavik", "Stuttgart"),
        ("Reykjavik", "Split"),
        ("Stuttgart", "Vienna"),
        ("Prague", "Manchester"),
        ("Edinburgh", "Prague"),
        ("Manchester", "Split"),
        ("Prague", "Vienna"),
        ("Vienna", "Manchester"),
        ("Prague", "Split"),
        ("Vienna", "Lyon"),
        ("Stuttgart", "Edinburgh"),
        ("Split", "Lyon"),
        ("Stuttgart", "Manchester"),
        ("Prague", "Lyon"),
        ("Reykjavik", "Vienna"),
        ("Prague", "Reykjavik"),
        ("Vienna", "Split"),
    ]
    direct_edges = set(frozenset(p) for p in direct_pairs)

    # Create CSP
    problem = Problem()
    pos_vars = [f"pos{i}" for i in range(len(cities))]

    # Each position in the sequence is a city; all different
    for var in pos_vars:
        problem.addVariable(var, cities)
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Direct flight constraint between consecutive positions
    def direct_flight(a, b, edges=direct_edges):
        return frozenset({a, b}) in edges

    for i in range(len(pos_vars) - 1):
        problem.addConstraint(direct_flight, (pos_vars[i], pos_vars[i + 1]))

    # Day placement constraints:
    # - Start on Day 1
    # - If you fly from city A to B on day X, you're in both on day X: implement as s[i+1] = e[i]
    # - Edinburgh must be Day 5-8 inclusive (4 days)
    # - Split must be Day 19-23 inclusive (5 days)
    # - Total calendar days must end at Day 25
    def day_constraints(*order):
        # order: tuple of city names in sequence
        start_day = 1
        city_to_range = {}
        for city in order:
            end_day = start_day + durations[city] - 1
            city_to_range[city] = (start_day, end_day)
            start_day = end_day  # overlap travel day

        # Validate required ranges
        if city_to_range["Edinburgh"] != (5, 8):
            return False
        if city_to_range["Split"] != (19, 23):
            return False

        # Final day must be Day 25
        if city_to_range[order[-1]][1] != total_days:
            return False

        return True

    problem.addConstraint(day_constraints, pos_vars)

    # Solve
    solutions = problem.getSolutions()

    if not solutions:
        output = {"itinerary": []}
        print(json.dumps(output))
        return

    # Choose the first solution and build the itinerary with day ranges
    sol = solutions[0]
    sequence = [sol[var] for var in pos_vars]

    itinerary = []
    start_day = 1
    for city in sequence:
        end_day = start_day + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })
        start_day = end_day  # overlap on flight day

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
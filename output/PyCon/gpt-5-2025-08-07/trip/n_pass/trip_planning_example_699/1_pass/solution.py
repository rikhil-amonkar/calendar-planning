import json
import sys

# Attempt to import python-constraint, install if missing
try:
    from constraint import Problem, AllDifferentConstraint
except ImportError:
    try:
        import subprocess
        subprocess.check_call([sys.executable, "-m", "pip", "install", "python-constraint"])
        from constraint import Problem, AllDifferentConstraint
    except Exception as e:
        print(json.dumps({"error": "python-constraint library is required"}))
        sys.exit(1)

def main():
    # Input variables (trip constraints)
    total_days = 16
    cities = ["Mykonos", "Reykjavik", "Dublin", "London", "Helsinki", "Hamburg"]
    durations = {
        "Mykonos": 3,
        "Reykjavik": 2,
        "Dublin": 5,
        "London": 5,
        "Helsinki": 4,
        "Hamburg": 2,
    }

    # Events/required presence windows (inclusive days)
    must_be_in_city_on_days = {
        "Dublin": list(range(2, 7)),      # Day 2-6 show in Dublin
        "Reykjavik": list(range(9, 11)),  # Wedding Day 9-10 in Reykjavik
        "Hamburg": list(range(1, 3)),     # Meet friends Day 1-2 in Hamburg
    }

    # Allowed direct flights (undirected)
    direct_pairs = [
        ("Dublin", "London"),
        ("Hamburg", "Dublin"),
        ("Helsinki", "Reykjavik"),
        ("Hamburg", "London"),
        ("Dublin", "Helsinki"),
        ("Reykjavik", "London"),
        ("London", "Mykonos"),
        ("Dublin", "Reykjavik"),
        ("Hamburg", "Helsinki"),
        ("Helsinki", "London"),
    ]
    direct_edges = set(frozenset(pair) for pair in direct_pairs)

    # Build CSP
    problem = Problem()
    pos_vars = [f"P{i}" for i in range(len(cities))]
    for v in pos_vars:
        problem.addVariable(v, cities)
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Single composite constraint to enforce:
    # - feasible direct flights between adjacent cities
    # - correct derived day ranges given durations and overlap rule
    # - presence windows (events) must be contained within city ranges
    # - total trip spans Day 1 to Day 16 with overlaps on flight days
    def schedule_constraint(*order_values):
        order = list(order_values)

        # Check adjacency has direct flights
        for i in range(len(order) - 1):
            if frozenset({order[i], order[i + 1]}) not in direct_edges:
                return False

        # Calculate starts/ends using overlap rule:
        # If fly from city A to city B on day X, then start_B = end_A = X
        starts = {}
        ends = {}

        current_start = 1  # Trip begins on Day 1
        for c in order:
            d = durations[c]
            s = current_start
            e = s + d - 1
            starts[c] = s
            ends[c] = e
            current_start = e  # next city's start overlaps on this end day

        # Ensure total trip ends on the last day
        if ends[order[-1]] != total_days:
            return False

        # Ensure all "must be in city on days" windows are satisfied
        for city, days in must_be_in_city_on_days.items():
            s, e = starts[city], ends[city]
            if min(days) < 1 or max(days) > total_days:
                return False
            if not (s <= min(days) and e >= max(days)):
                return False

        # Optional sanity: Hamburg should naturally start Day 1 due to constraints
        if starts["Hamburg"] != 1:
            return False

        # Check that sum of durations minus overlaps matches total_days
        sum_durations = sum(durations.values())
        # With n cities chained, there are exactly (n-1) overlaps
        expected_end = 1 + sum_durations - len(cities)
        if expected_end != total_days:
            return False

        return True

    problem.addConstraint(schedule_constraint, pos_vars)

    solutions = problem.getSolutions()

    if not solutions:
        print(json.dumps({"error": "No feasible itinerary found with given constraints"}))
        return

    # Choose one solution (e.g., the first)
    solution = solutions[0]
    ordered_cities = [solution[f"P{i}"] for i in range(len(cities))]

    # Recompute starts/ends to format itinerary
    starts = {}
    ends = {}
    s = 1
    for c in ordered_cities:
        e = s + durations[c] - 1
        starts[c] = s
        ends[c] = e
        s = e

    itinerary = []
    for c in ordered_cities:
        itinerary.append({
            "day_range": f"Day {starts[c]}-{ends[c]}",
            "place": c
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
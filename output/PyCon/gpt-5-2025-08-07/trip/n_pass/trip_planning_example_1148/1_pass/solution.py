import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and durations (in days)
    cities = ["Lisbon", "Dubrovnik", "Copenhagen", "Prague", "Tallinn", "Stockholm", "Split", "Lyon"]
    durations = {
        "Lisbon": 2,
        "Dubrovnik": 5,
        "Copenhagen": 5,
        "Prague": 3,
        "Tallinn": 2,
        "Stockholm": 4,
        "Split": 3,
        "Lyon": 2
    }

    # Direct flight edges (undirected)
    direct_pairs = [
        ("Dubrovnik", "Stockholm"),
        ("Lisbon", "Copenhagen"),
        ("Lisbon", "Lyon"),
        ("Copenhagen", "Stockholm"),
        ("Copenhagen", "Split"),
        ("Prague", "Stockholm"),
        ("Tallinn", "Stockholm"),
        ("Prague", "Lyon"),
        ("Lisbon", "Stockholm"),
        ("Prague", "Lisbon"),
        ("Stockholm", "Split"),
        ("Prague", "Copenhagen"),
        ("Split", "Lyon"),
        ("Copenhagen", "Dubrovnik"),
        ("Prague", "Split"),
        ("Tallinn", "Copenhagen"),
        ("Tallinn", "Prague"),
    ]
    direct_edges = set(frozenset(p) for p in direct_pairs)

    total_days = 19

    problem = Problem()

    # Position variables (order of visiting 8 cities)
    pos_vars = [f"pos{i}" for i in range(1, 9)]
    for v in pos_vars:
        problem.addVariable(v, cities)
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Start day variables for each segment
    start_vars = [f"s{i}" for i in range(1, 9)]
    for s in start_vars:
        problem.addVariable(s, range(1, total_days + 1))

    # Start on Day 1
    problem.addConstraint(lambda s: s == 1, ("s1",))

    # City-specific fixed windows:
    # - Tallinn must include days 1-2 (duration 2) => start at 1
    # - Lisbon must include days 4-5 (duration 2) => start at 4
    # - Stockholm must include days 13-16 (duration 4) => start at 13
    # - Lyon must include days 18-19 (duration 2) => start at 18
    def city_window_constraint(city, s):
        if city == "Tallinn":
            return s == 1
        if city == "Lisbon":
            return s == 4
        if city == "Stockholm":
            return s == 13
        if city == "Lyon":
            return s == 18
        return True

    for i in range(1, 9):
        problem.addConstraint(city_window_constraint, (f"pos{i}", f"s{i}"))

    # Chain constraints: next segment starts on the same day the previous ends (flight day overlap)
    # s_{i+1} = s_i + duration(city_i) - 1
    for i in range(1, 8):
        problem.addConstraint(
            lambda city_i, s_i, s_next, durations=durations: s_next == s_i + durations[city_i] - 1,
            (f"pos{i}", f"s{i}", f"s{i+1}")
        )

    # Direct flight constraints between consecutive cities
    for i in range(1, 8):
        problem.addConstraint(
            lambda a, b, edges=direct_edges: frozenset((a, b)) in edges,
            (f"pos{i}", f"pos{i+1}")
        )

    # Ensure the final segment ends exactly on Day 19
    problem.addConstraint(
        lambda city, s, durations=durations: s + durations[city] - 1 == total_days,
        ("pos8", "s8")
    )

    # Solve
    solution = problem.getSolution()

    if not solution:
        print(json.dumps({"itinerary": []}))
        return

    # Build itinerary
    itinerary = []
    for i in range(1, 9):
        city = solution[f"pos{i}"]
        s = solution[f"s{i}"]
        e = s + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    # Sort itinerary by start day just in case
    itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split('-')[0]))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
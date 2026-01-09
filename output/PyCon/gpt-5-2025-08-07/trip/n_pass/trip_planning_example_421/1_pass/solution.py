import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables and constraints
    total_days = 20
    cities = ["Nice", "Dublin", "Krakow", "Lyon", "Frankfurt"]
    durations = {
        "Nice": 5,
        "Krakow": 6,
        "Dublin": 7,
        "Lyon": 4,
        "Frankfurt": 2,
    }
    # Meeting/visit constraints
    nice_meet_window = (1, 5)       # relatives in Nice between day 1 and 5
    frankfurt_meet_window = (19, 20) # friends in Frankfurt between day 19 and 20

    # Undirected edges with direct flights
    direct_edges = {
        frozenset(("Nice", "Dublin")),
        frozenset(("Dublin", "Frankfurt")),
        frozenset(("Dublin", "Krakow")),
        frozenset(("Krakow", "Frankfurt")),
        frozenset(("Lyon", "Frankfurt")),
        frozenset(("Nice", "Frankfurt")),
        frozenset(("Lyon", "Dublin")),
        frozenset(("Nice", "Lyon")),
    }

    # Set up CSP with python-constraint
    problem = Problem()
    slots = ["S1", "S2", "S3", "S4", "S5"]
    # Domains
    problem.addVariable("S1", ["Nice"])
    problem.addVariable("S5", ["Frankfurt"])
    for s in ["S2", "S3", "S4"]:
        problem.addVariable(s, cities)
    # All different (each city exactly once)
    problem.addConstraint(AllDifferentConstraint(), slots)

    # Adjacency constraints (direct flights between consecutive cities)
    for a, b in zip(slots[:-1], slots[1:]):
        problem.addConstraint(lambda x, y, edges=direct_edges: frozenset((x, y)) in edges, (a, b))

    # Global schedule constraint to ensure day windows and total coverage
    def schedule_constraint(s1, s2, s3, s4, s5):
        order = [s1, s2, s3, s4, s5]
        # Build intervals using overlap rule (next starts on previous end day)
        intervals = {}
        start = 1
        for city in order:
            end = start + durations[city] - 1
            intervals[city] = (start, end)
            start = end  # overlap on transition day

        # Ensure overall coverage is exactly total_days
        if intervals[order[-1]][1] != total_days:
            return False

        # Ensure Nice visit window is covered and duration is 5 days
        n_s, n_e = intervals["Nice"]
        if not (n_s <= nice_meet_window[0] and n_e >= nice_meet_window[1]):
            return False

        # Ensure Frankfurt meet window is covered and duration is 2 days
        f_s, f_e = intervals["Frankfurt"]
        if not (f_s <= frankfurt_meet_window[0] and f_e >= frankfurt_meet_window[1]):
            return False

        return True

    problem.addConstraint(schedule_constraint, tuple(slots))

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        print(json.dumps({"error": "No feasible itinerary satisfying the constraints."}))
        return

    # Choose first valid solution
    sol = solutions[0]
    order = [sol["S1"], sol["S2"], sol["S3"], sol["S4"], sol["S5"]]

    # Build itinerary with actual day ranges using overlap rule
    itinerary = []
    start = 1
    for city in order:
        end = start + durations[city] - 1
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
        start = end  # overlap next city's start at current end

    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()
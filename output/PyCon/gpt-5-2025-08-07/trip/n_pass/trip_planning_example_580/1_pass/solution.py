import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables (constraints)
    total_days = 23
    cities = ["Paris", "Oslo", "Porto", "Geneva", "Reykjavik"]
    durations = {
        "Paris": 6,
        "Oslo": 5,
        "Porto": 7,
        "Geneva": 7,
        "Reykjavik": 2
    }
    # Direct flight pairs (undirected)
    direct_flights_pairs = [
        ("Paris", "Oslo"),
        ("Geneva", "Oslo"),
        ("Porto", "Paris"),
        ("Geneva", "Paris"),
        ("Geneva", "Porto"),
        ("Paris", "Reykjavik"),
        ("Reykjavik", "Oslo"),
        ("Porto", "Oslo"),
    ]
    direct_flights = set(frozenset(p) for p in direct_flights_pairs)

    # Conference and visiting relatives constraints
    conference_days_geneva = [1, 7]
    oslo_visit_window = (19, 23)  # inclusive

    # Configure the CSP
    problem = Problem()
    position_vars = ["pos1", "pos2", "pos3", "pos4", "pos5"]
    for var in position_vars:
        problem.addVariable(var, cities)
    problem.addConstraint(AllDifferentConstraint(), position_vars)

    # Must start in Geneva on Day 1 (conference) and end in Oslo (relatives)
    problem.addConstraint(lambda c: c == "Geneva", ("pos1",))
    problem.addConstraint(lambda c: c == "Oslo", ("pos5",))

    # Only direct flights between consecutive cities
    for i in range(1, 5):
        problem.addConstraint(
            lambda a, b, df=direct_flights: frozenset((a, b)) in df,
            (f"pos{i}", f"pos{i+1}")
        )

    # Global constraint to enforce day accounting, durations, and date-specific requirements
    def sequence_and_time_constraint(p1, p2, p3, p4, p5):
        seq = [p1, p2, p3, p4, p5]

        # Validate adjacency again (redundant but keeps this constraint self-contained)
        for (a, b) in zip(seq, seq[1:]):
            if frozenset((a, b)) not in direct_flights:
                return False

        # Build start/end days using the overlap rule: next start = current end (same-day travel)
        start = {}
        end = {}
        current_start = 1
        for city in seq:
            start[city] = current_start
            end[city] = current_start + durations[city] - 1
            current_start = end[city]  # next city starts on the same day as end (travel day counts for both)

        # Ensure the overall timeline matches total_days
        if end[seq[-1]] != total_days:
            return False

        # Geneva conference days must be included
        # Given Geneva must be first, this enforces Geneva covers Days 1 through 7 exactly
        for d in conference_days_geneva:
            if not (start["Geneva"] <= d <= end["Geneva"]):
                return False

        # Oslo visit days constrained to 19-23 inclusive and 5 days total
        if not (start["Oslo"] == oslo_visit_window[0] and end["Oslo"] == oslo_visit_window[1]):
            return False

        # Durations integrity (implicit by construction)
        if any((end[c] - start[c] + 1) != durations[c] for c in durations):
            return False

        # Ensure the chain is a valid permutation of the cities list
        if set(seq) != set(cities):
            return False

        return True

    problem.addConstraint(sequence_and_time_constraint, position_vars)

    solutions = problem.getSolutions()

    if not solutions:
        print(json.dumps({"itinerary": [], "status": "no_solution"}))
        return

    # Choose the first solution (deterministic because the solution is unique under given constraints)
    sol = solutions[0]
    sequence = [sol[f"pos{i}"] for i in range(1, 6)]

    # Compute the day ranges for the itinerary
    start_day = 1
    itinerary = []
    for city in sequence:
        end_day = start_day + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })
        start_day = end_day  # next city starts on the same day as end (travel day counts for both)

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
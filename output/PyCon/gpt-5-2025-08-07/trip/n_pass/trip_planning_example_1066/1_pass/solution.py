import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and required durations (days counted including overlap travel days)
    cities = ["Brussels", "Bucharest", "Stuttgart", "Mykonos", "Madrid", "Helsinki", "Split", "London"]
    durations = {
        "Brussels": 4,
        "Bucharest": 3,
        "Stuttgart": 4,
        "Mykonos": 2,
        "Madrid": 2,     # Must be Day 20-21 (conference)
        "Helsinki": 5,
        "Split": 3,
        "London": 5
    }

    # Direct flights (undirected edges)
    flight_pairs = [
        ("Helsinki", "London"),
        ("Split", "Madrid"),
        ("Helsinki", "Madrid"),
        ("London", "Madrid"),
        ("Brussels", "London"),
        ("Bucharest", "London"),
        ("Brussels", "Bucharest"),
        ("Bucharest", "Madrid"),
        ("Split", "Helsinki"),
        ("Mykonos", "Madrid"),
        ("Stuttgart", "London"),
        ("Helsinki", "Brussels"),
        ("Brussels", "Madrid"),
        ("Split", "London"),
        ("Stuttgart", "Split"),
        ("London", "Mykonos"),
    ]
    edges = set(frozenset((a, b)) for a, b in flight_pairs)

    # Create a CSP with 8 ordered positions (pos1..pos8) representing the visit sequence
    pos_vars = [f"pos{i}" for i in range(1, 9)]
    problem = Problem()
    # All positions can be any city initially
    for v in pos_vars:
        problem.addVariable(v, cities)
    # Madrid must be visited last to ensure Day 20-21 in Madrid
    problem.addConstraint(lambda v: v == "Madrid", ("pos8",))
    # All positions must be different (visit each city exactly once)
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Consecutive positions must have a direct flight (only direct flights between cities)
    def adjacent(a, b):
        return frozenset((a, b)) in edges

    for i in range(1, 8):
        problem.addConstraint(adjacent, (f"pos{i}", f"pos{i+1}"))

    # Global timing constraint:
    # - Build day ranges using overlaps (transition day counts for both cities)
    # - Stuttgart must include at least one day in [1..4]
    def time_constraints(*order_vals):
        order = list(order_vals)  # [pos1, pos2, ..., pos8] mapped to city names
        # Compute start/end days with overlap rule:
        # S1 = 1; Ei = Si + Li - 1; S(i+1) = Ei (overlap travel day)
        starts, ends = {}, {}
        s = 1
        for city in order:
            starts[city] = s
            ends[city] = s + durations[city] - 1
            s = ends[city]  # overlap to next segment

        # Ensure Stuttgart includes at least one day between Day 1 and Day 4
        st_s, st_e = starts["Stuttgart"], ends["Stuttgart"]
        meets_friend = (st_s <= 4 and st_e >= 1)

        # Ensure total calendar days end at Day 21 (implicit from durations and overlaps)
        # With 8 cities and overlaps, final end must be 21
        timeline_ok = (ends[order[-1]] == 21)

        # End city is Madrid (already constrained) thus Madrid spans Day 20-21 automatically for 2 days
        # Still assert for robustness
        madrid_ok = (starts["Madrid"] == 20 and ends["Madrid"] == 21)

        return meets_friend and timeline_ok and madrid_ok

    problem.addConstraint(time_constraints, tuple(pos_vars))

    solutions = problem.getSolutions()
    if not solutions:
        print(json.dumps({"error": "No feasible itinerary found with the given constraints."}))
        return

    # Choose the first solution (any feasible solution is acceptable)
    sol = solutions[0]
    ordered_cities = [sol[f"pos{i}"] for i in range(1, 9)]

    # Build the itinerary with computed day ranges
    itinerary = []
    start_day = 1
    for city in ordered_cities:
        end_day = start_day + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })
        start_day = end_day  # overlap next segment on the same day

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and required stay durations (in days)
    cities = [
        "Berlin", "Stockholm", "Zurich", "Lyon", "Paris",
        "Riga", "Nice", "Seville", "Milan", "Naples"
    ]
    durations = {
        "Lyon": 3,
        "Paris": 5,
        "Riga": 2,
        "Berlin": 2,
        "Stockholm": 3,
        "Zurich": 5,
        "Nice": 2,
        "Seville": 3,
        "Milan": 3,
        "Naples": 4
    }

    # Direct flight pairs (treated as undirected)
    direct_pairs = [
        ("Paris", "Stockholm"), ("Seville", "Paris"), ("Naples", "Zurich"),
        ("Nice", "Riga"), ("Berlin", "Milan"), ("Paris", "Zurich"),
        ("Paris", "Nice"), ("Milan", "Paris"), ("Milan", "Riga"),
        ("Paris", "Lyon"), ("Milan", "Naples"), ("Paris", "Riga"),
        ("Berlin", "Stockholm"), ("Stockholm", "Riga"), ("Nice", "Zurich"),
        ("Milan", "Zurich"), ("Lyon", "Nice"), ("Zurich", "Stockholm"),
        ("Zurich", "Riga"), ("Berlin", "Naples"), ("Milan", "Stockholm"),
        ("Berlin", "Zurich"), ("Milan", "Seville"), ("Paris", "Naples"),
        ("Berlin", "Riga"), ("Nice", "Stockholm"), ("Berlin", "Paris"),
        ("Nice", "Naples"), ("Berlin", "Nice")
    ]
    # Convert to undirected adjacency set
    direct_set = set()
    for a, b in direct_pairs:
        direct_set.add(tuple(sorted((a, b))))

    # Precompute (duration - 1) for telescoping day starts
    delta = {c: durations[c] - 1 for c in cities}

    # Total days and telescoping property:
    total_days = 23
    # Sum of durations is 32; with 10 cities, final day should be 32 - 9 = 23, consistent.

    # Constraint problem: positions 1..10 for each city (permutation)
    problem = Problem()
    for c in cities:
        problem.addVariable(f"pos_{c}", range(1, 11))
    problem.addConstraint(AllDifferentConstraint(), [f"pos_{c}" for c in cities])

    # Helper to build a single global constraint over all position variables
    var_names = [f"pos_{c}" for c in cities]

    def global_constraint(*pos_values):
        pos = {city: val for city, val in zip(cities, pos_values)}

        # Berlin must be first to cover Days 1-2 wedding in Berlin
        if pos["Berlin"] != 1:
            return False

        # Build order: position -> city
        order = [None] * 10
        for c in cities:
            p = pos[c]
            if not (1 <= p <= 10):
                return False
            order[p - 1] = c

        # Check all positions filled
        if any(x is None for x in order):
            return False

        # Check direct flights between consecutive cities
        for i in range(9):
            a, b = order[i], order[i + 1]
            if tuple(sorted((a, b))) not in direct_set:
                return False

        # Compute start and end days via telescoping:
        # s1 = 1; s_{i+1} = e_i = s_i + duration_i - 1
        start_day = {}
        end_day = {}
        current_start = 1
        for idx, c in enumerate(order):
            start_day[c] = current_start
            end_day[c] = current_start + durations[c] - 1
            current_start = end_day[c]  # next start equals today's end (flight day counts both)

        # Final day must be 23
        if end_day[order[-1]] != total_days:
            return False

        # Fixed-date constraints:
        # Nice workshop on days 12-13 => Nice's block must be exactly days 12-13
        if not (start_day["Nice"] == 12 and end_day["Nice"] == 13):
            return False

        # Stockholm show on days 20-22 => Stockholm's block must be exactly days 20-22
        if not (start_day["Stockholm"] == 20 and end_day["Stockholm"] == 22):
            return False

        # Berlin wedding on days 1-2 satisfied by Berlin first with duration 2 (already enforced by Berlin first)
        if not (start_day["Berlin"] == 1 and end_day["Berlin"] == 2):
            return False

        # All city durations are already encoded by construction; implicit constraints satisfied.

        return True

    problem.addConstraint(global_constraint, var_names)

    solutions = problem.getSolutions()

    if not solutions:
        raise RuntimeError("No valid itinerary found with the given constraints.")

    # Choose the first solution
    sol = solutions[0]
    # Build ordered list by positions
    ordered = sorted(((sol[f"pos_{c}"], c) for c in cities), key=lambda x: x[0])
    itinerary = []
    # Compute start/end using telescoping rule
    current_start = 1
    for _, c in ordered:
        start = current_start
        end = start + durations[c] - 1
        itinerary.append({"day_range": f"Day {start}-{end}", "place": c})
        current_start = end  # next starts at today's end (flight day double-count)

    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()
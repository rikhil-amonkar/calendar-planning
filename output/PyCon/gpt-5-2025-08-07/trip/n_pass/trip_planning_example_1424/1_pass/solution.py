import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and required durations (in days counted with flight-day overlap rules)
    cities = [
        "Warsaw", "Porto", "Naples", "Brussels", "Split",
        "Reykjavik", "Amsterdam", "Lyon", "Helsinki", "Valencia"
    ]
    durations = {
        "Warsaw": 3,
        "Porto": 5,
        "Naples": 4,
        "Brussels": 3,
        "Split": 3,
        "Reykjavik": 5,
        "Amsterdam": 4,
        "Lyon": 3,
        "Helsinki": 4,
        "Valencia": 2,
    }
    total_days = 27  # Trip length

    # Direct flights (undirected)
    flight_pairs = [
        ("Amsterdam", "Warsaw"),
        ("Helsinki", "Brussels"),
        ("Helsinki", "Warsaw"),
        ("Reykjavik", "Brussels"),
        ("Amsterdam", "Lyon"),
        ("Amsterdam", "Naples"),
        ("Amsterdam", "Reykjavik"),
        ("Naples", "Valencia"),
        ("Porto", "Brussels"),
        ("Amsterdam", "Split"),
        ("Lyon", "Split"),
        ("Warsaw", "Split"),
        ("Porto", "Amsterdam"),
        ("Helsinki", "Split"),
        ("Brussels", "Lyon"),
        ("Porto", "Lyon"),
        ("Reykjavik", "Warsaw"),
        ("Brussels", "Valencia"),
        ("Valencia", "Lyon"),
        ("Porto", "Warsaw"),
        ("Warsaw", "Valencia"),
        ("Amsterdam", "Helsinki"),
        ("Porto", "Valencia"),
        ("Warsaw", "Brussels"),
        ("Warsaw", "Naples"),
        ("Naples", "Split"),
        ("Helsinki", "Naples"),
        ("Helsinki", "Reykjavik"),
        ("Amsterdam", "Valencia"),
        ("Naples", "Brussels"),
    ]
    flights = {frozenset(p) for p in flight_pairs}

    # Helper to compute start day for a city at position k given a sequence prefix
    def start_day_for_position(prefix_cities):
        # prefix_cities: list of cities in positions 0..k-1 (k items)
        return 1 + sum(durations[c] - 1 for c in prefix_cities)

    # Create CSP
    problem = Problem()
    position_vars = [f"pos{i}" for i in range(10)]
    for var in position_vars:
        problem.addVariable(var, cities)

    # All cities must be unique in the sequence (visit each city exactly once)
    problem.addConstraint(AllDifferentConstraint(), position_vars)

    # Adjacency must be connected by a direct flight
    def adjacency_constraint(a, b):
        return frozenset([a, b]) in flights

    for i in range(9):
        problem.addConstraint(adjacency_constraint, (position_vars[i], position_vars[i + 1]))

    # Prefix constraints to handle time windows and fixed start days
    # - Porto must intersect [1,5]
    # - Amsterdam must intersect [5,8]
    # - Helsinki must intersect [8,11]
    # - Naples must start at day 17 (covers 17..20)
    # - Brussels must start at day 20 (covers 20..22)
    def make_prefix_constraint(i):
        def constraint(*vals):
            seq = list(vals)  # cities at positions 0..i
            city = seq[-1]
            start = start_day_for_position(seq[:-1])
            end = start + durations[city] - 1

            ok = True
            # Porto workshop between day 1 and day 5 (inclusive) -> intersection with [1,5]
            if city == "Porto":
                ok = ok and not (end < 1 or start > 5)
            # Amsterdam relatives between day 5 and day 8 -> intersection with [5,8]
            if city == "Amsterdam":
                ok = ok and not (end < 5 or start > 8)
            # Helsinki wedding between day 8 and day 11 -> intersection with [8,11]
            if city == "Helsinki":
                ok = ok and not (end < 8 or start > 11)
            # Naples conference on days 17 and 20 -> start must be 17 (duration 4 -> 17..20)
            if city == "Naples":
                ok = ok and (start == 17)
            # Brussels show from day 20 to 22 -> start must be 20 (duration 3 -> 20..22)
            if city == "Brussels":
                ok = ok and (start == 20)

            # Ensure stays are within 1..27 when placed (conservative check)
            # Start must be >= 1 (guaranteed) and end <= 27 is required only for the final cumulative,
            # but checking doesn't hurt because cumulative is fixed by durations.
            ok = ok and (start >= 1) and (end <= total_days)

            return ok
        return constraint

    for i in range(10):
        problem.addConstraint(make_prefix_constraint(i), tuple(position_vars[: i + 1]))

    # Solve
    solution = problem.getSolution()
    if not solution:
        raise RuntimeError("No valid itinerary found with the given constraints.")

    # Build ordered sequence
    ordered = [None] * 10
    for var, city in solution.items():
        idx = int(var.replace("pos", ""))
        ordered[idx] = city

    # Compute day ranges using overlap rule (flight day counts for both cities)
    itinerary = []
    current_start = 1
    for city in ordered:
        start = current_start
        end = start + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
        # Next city starts on the same day as end (flight day overlaps both cities)
        current_start = end

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Cities and durations (inclusive of both start and end days)
    cities = ["Oslo", "Dubrovnik", "Helsinki", "Krakow", "Vilnius", "Paris", "Madrid", "Mykonos"]
    durations = {
        "Oslo": 2,
        "Dubrovnik": 3,
        "Helsinki": 2,
        "Krakow": 5,
        "Vilnius": 2,
        "Paris": 2,
        "Madrid": 5,
        "Mykonos": 4,
    }

    # Direct flight connections (treated as undirected)
    flight_pairs = [
        ("Oslo", "Krakow"),
        ("Oslo", "Paris"),
        ("Paris", "Madrid"),
        ("Helsinki", "Vilnius"),
        ("Oslo", "Madrid"),
        ("Oslo", "Helsinki"),
        ("Helsinki", "Krakow"),
        ("Dubrovnik", "Helsinki"),
        ("Dubrovnik", "Madrid"),
        ("Oslo", "Dubrovnik"),
        ("Krakow", "Paris"),
        ("Madrid", "Mykonos"),
        ("Oslo", "Vilnius"),
        ("Krakow", "Vilnius"),  # treated undirected
        ("Helsinki", "Paris"),
        ("Vilnius", "Paris"),
        ("Helsinki", "Madrid"),
    ]
    flights = set()
    for a, b in flight_pairs:
        flights.add((a, b))
        flights.add((b, a))

    # Problem setup
    problem = Problem()

    # Variables: start day for each city (1..18), and position in chain (1..8)
    for c in cities:
        problem.addVariable(f"start_{c}", range(1, 19))
    # Positions (sequence order of visiting cities)
    for c in cities:
        problem.addVariable(f"pos_{c}", range(1, 9))

    # Positions must be a permutation of 1..8
    problem.addConstraint(AllDifferentConstraint(), [f"pos_{c}" for c in cities])

    # Fixed timing constraints from the problem statement
    # - Trip starts in Oslo to meet friends on days 1 and 2 (so Oslo is days 1-2)
    problem.addConstraint(lambda s: s == 1, [f"start_Oslo"])
    # - Dubrovnik days 2-4 to attend the show
    problem.addConstraint(lambda s: s == 2, [f"start_Dubrovnik"])
    # - Mykonos with relatives days 15-18
    problem.addConstraint(lambda s: s == 15, [f"start_Mykonos"])

    # Fixed order constraints implied by timing:
    # Oslo first, Dubrovnik second (attend show day 2-4), Madrid must be right before Mykonos (direct flight)
    problem.addConstraint(lambda p: p == 1, [f"pos_Oslo"])
    problem.addConstraint(lambda p: p == 2, [f"pos_Dubrovnik"])
    problem.addConstraint(lambda p: p == 7, [f"pos_Madrid"])
    problem.addConstraint(lambda p: p == 8, [f"pos_Mykonos"])

    # Restrict remaining city positions to 3..6
    for c in ["Helsinki", "Krakow", "Vilnius", "Paris"]:
        problem.addConstraint(lambda p: 3 <= p <= 6, [f"pos_{c}"])

    # Global chain constraint: ensure contiguous 1-day overlaps and direct flights between consecutive cities
    start_vars = [f"start_{c}" for c in cities]
    pos_vars = [f"pos_{c}" for c in cities]
    all_vars = start_vars + pos_vars

    def chain_constraint(*values):
        # Map variable names to values
        vals = dict(zip(all_vars, values))
        # Build maps for starts and positions
        start = {c: vals[f"start_{c}"] for c in cities}
        pos = {c: vals[f"pos_{c}"] for c in cities}

        # Ensure positions form a proper chain mapping
        pos_to_city = {pos[c]: c for c in cities}
        if set(pos_to_city.keys()) != set(range(1, 9)):
            return False

        # Check chain adjacency: direct flights and 1-day overlap transitions
        for i in range(1, 8):
            a = pos_to_city[i]
            b = pos_to_city[i + 1]
            # Direct flight requirement
            if (a, b) not in flights:
                return False
            # One-day overlap: start[next] = end[current] = start[current] + dur[current] - 1
            if start[b] != start[a] + durations[a] - 1:
                return False

        # Ensure all date ranges fall within 1..18
        for c in cities:
            end_c = start[c] + durations[c] - 1
            if not (1 <= start[c] <= 18 and 1 <= end_c <= 18):
                return False

        # Verify specific window constraints are satisfied explicitly
        # Oslo days 1-2
        if not (start["Oslo"] == 1 and start["Oslo"] + durations["Oslo"] - 1 == 2):
            return False
        # Dubrovnik days 2-4
        if not (start["Dubrovnik"] == 2 and start["Dubrovnik"] + durations["Dubrovnik"] - 1 == 4):
            return False
        # Mykonos days 15-18
        if not (start["Mykonos"] == 15 and start["Mykonos"] + durations["Mykonos"] - 1 == 18):
            return False

        # Ensure chain starts on day 1 and ends on day 18
        first_city = pos_to_city[1]
        last_city = pos_to_city[8]
        if start[first_city] != 1:
            return False
        if start[last_city] + durations[last_city] - 1 != 18:
            return False

        return True

    problem.addConstraint(chain_constraint, all_vars)

    # Solve
    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"itinerary": []}))
        return

    # Build itinerary from solution
    start = {c: solution[f"start_{c}"] for c in cities}
    pos = {c: solution[f"pos_{c}"] for c in cities}
    itinerary_order = sorted(cities, key=lambda c: pos[c])

    itinerary = []
    for c in itinerary_order:
        s = start[c]
        e = s + durations[c] - 1
        itinerary.append({"day_range": f"Day {s}-{e}", "place": c})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
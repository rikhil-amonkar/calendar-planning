import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Cities and required durations (inclusive day counts)
    durations = {
        "Valencia": 2,
        "Oslo": 3,
        "Lyon": 4,
        "Prague": 3,
        "Paris": 4,
        "Nice": 4,
        "Seville": 5,
        "Tallinn": 2,
        "Mykonos": 5,
        "Lisbon": 2,
    }
    cities = list(durations.keys())

    # Direct flights (undirected)
    edges_list = [
        ("Lisbon", "Paris"),
        ("Lyon", "Nice"),
        ("Tallinn", "Oslo"),
        ("Prague", "Lyon"),
        ("Paris", "Oslo"),
        ("Lisbon", "Seville"),
        ("Prague", "Lisbon"),
        ("Oslo", "Nice"),
        ("Valencia", "Paris"),
        ("Valencia", "Lisbon"),
        ("Paris", "Nice"),
        ("Nice", "Mykonos"),
        ("Paris", "Lyon"),
        ("Valencia", "Lyon"),
        ("Prague", "Oslo"),
        ("Prague", "Paris"),
        ("Seville", "Paris"),
        ("Oslo", "Lyon"),
        ("Prague", "Valencia"),
        ("Lisbon", "Nice"),
        ("Lisbon", "Oslo"),
        ("Valencia", "Seville"),
        ("Lisbon", "Lyon"),
        ("Paris", "Tallinn"),
        ("Prague", "Tallinn"),
    ]
    # Build undirected adjacency set
    adjacency = set()
    for a, b in edges_list:
        adjacency.add((a, b))
        adjacency.add((b, a))

    # Helper: compute start days given an ordering by positions
    def compute_start_days(pos_assignment):
        # pos_assignment: dict city -> position (1..10)
        ordered = sorted(pos_assignment.items(), key=lambda kv: kv[1])  # sort by position
        start_days = {}
        start = 1
        for city, _ in ordered:
            start_days[city] = start
            start = start + durations[city] - 1  # next segment starts at current end day
        return start_days, [c for c, _ in ordered]

    problem = Problem()

    # Variables: position of each city in the sequence (1..10)
    for c in cities:
        problem.addVariable(f"pos_{c}", range(1, len(cities) + 1))

    # All positions must be different
    problem.addConstraint(AllDifferentConstraint(), [f"pos_{c}" for c in cities])

    # Adjacency (direct flights) constraints for neighboring positions
    def neighbor_constraint(a, b, city_a, city_b):
        # If city_b immediately follows city_a, there must be a direct flight
        if a + 1 == b:
            return (city_a, city_b) in adjacency
        if b + 1 == a:
            return (city_b, city_a) in adjacency
        return True

    # Add pairwise constraints for all city pairs to prune search early
    for i in range(len(cities)):
        for j in range(i + 1, len(cities)):
            ca = cities[i]
            cb = cities[j]
            problem.addConstraint(
                lambda a, b, ca=ca, cb=cb: neighbor_constraint(a, b, ca, cb),
                (f"pos_{ca}", f"pos_{cb}")
            )

    # Global constraint to enforce day anchors and Seville show overlap
    def global_constraints(*pos_values):
        pos_assignment = {city: pos_values[idx] for idx, city in enumerate(cities)}
        # Quick validity check: all positions 1..10 unique done by AllDifferent
        # Compute start days from positions and durations chain
        start_days, ordered_cities = compute_start_days(pos_assignment)

        # Validate direct flights for consecutive ordered cities (redundant but safe)
        for k in range(len(ordered_cities) - 1):
            a = ordered_cities[k]
            b = ordered_cities[k + 1]
            if (a, b) not in adjacency:
                return False

        # Anchor constraints:
        # Valencia for 2 days and meet between day 3 and 4 -> exactly days 3-4
        if start_days["Valencia"] != 3:
            return False

        # Oslo for 3 days and meet between day 13 and 15 -> exactly days 13-15
        if start_days["Oslo"] != 13:
            return False

        # Mykonos for 5 days with wedding between day 21 and 25 -> exactly days 21-25
        if start_days["Mykonos"] != 21:
            return False

        # Seville 5 days overlapping the show window [5,9]
        s_sev = start_days["Seville"]
        e_sev = s_sev + durations["Seville"] - 1
        # overlap condition with [5,9]
        if e_sev < 5 or s_sev > 9:
            return False

        # The unique day span should be exactly 25 by construction; verify last end day is 25
        last_city = ordered_cities[-1]
        end_last = start_days[last_city] + durations[last_city] - 1
        if start_days[ordered_cities[0]] != 1 or end_last != 25:
            return False

        return True

    problem.addConstraint(
        global_constraints,
        tuple(f"pos_{c}" for c in cities)
    )

    solution = problem.getSolution()
    if not solution:
        # If no solution found (should not happen with given constraints), output empty itinerary
        print(json.dumps({"itinerary": []}))
        return

    # Build itinerary from the solution
    # Sort cities by position
    ordered = sorted(((city, solution[f"pos_{city}"]) for city in cities), key=lambda x: x[1])
    itinerary = []
    start = 1
    for city, _ in ordered:
        s = start
        e = s + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })
        start = e  # next segment starts at the end day (overlap due to flight day)

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
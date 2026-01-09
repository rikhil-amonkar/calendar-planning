import json
from constraint import Problem

def main():
    # Input Variables
    total_days = 12
    cities = ["Hamburg", "Zurich", "Helsinki", "Bucharest", "Split"]
    durations = {
        "Hamburg": 2,
        "Zurich": 3,
        "Helsinki": 2,
        "Bucharest": 2,
        "Split": 7,
    }

    # Direct flight edges (undirected)
    direct_pairs = [
        ("Zurich", "Helsinki"),
        ("Hamburg", "Bucharest"),
        ("Helsinki", "Hamburg"),
        ("Zurich", "Hamburg"),
        ("Zurich", "Bucharest"),
        ("Zurich", "Split"),
        ("Helsinki", "Split"),
        ("Split", "Hamburg"),
    ]
    edges = set(frozenset(pair) for pair in direct_pairs)

    days = list(range(1, total_days + 1))

    problem = Problem()
    problem.addVariable("Start", cities)
    for d in days:
        problem.addVariable(f"D{d}", cities)

    # No flight on day 1 to ensure we can meet multi-day durations; Start equals Day1
    problem.addConstraint(lambda s, d1: s == d1, ("Start", "D1"))

    # Allowed flights or stay between consecutive days (d>=2)
    def allowed_transition(a, b, edges=edges):
        return a == b or (frozenset({a, b}) in edges)

    for d in range(2, total_days + 1):
        problem.addConstraint(allowed_transition, (f"D{d-1}", f"D{d}"))

    # Conference in Split on day 4: presence on day 4
    # Presence on day d in city C if Dd == C OR (D(d-1) == C and Dd != D(d-1))
    problem.addConstraint(
        lambda d3, d4: (d4 == "Split") or (d3 == "Split" and d4 != d3),
        ("D3", "D4"),
    )

    # Conference in Split on day 10: presence on day 10
    problem.addConstraint(
        lambda d9, d10: (d10 == "Split") or (d9 == "Split" and d10 != d9),
        ("D9", "D10"),
    )

    # Wedding in Zurich between Day 1 and Day 3: presence on at least one of the days
    def zurich_wedding(start, d1, d2, d3):
        pres1 = (d1 == "Zurich") or (start == "Zurich" and d1 != start)
        pres2 = (d2 == "Zurich") or (d1 == "Zurich" and d2 != d1)
        pres3 = (d3 == "Zurich") or (d2 == "Zurich" and d3 != d2)
        return pres1 or pres2 or pres3

    problem.addConstraint(zurich_wedding, ("Start", "D1", "D2", "D3"))

    # Global constraint: exact durations and exactly 4 travel days
    def global_constraint(*vals):
        # Map variable names to values
        var_names = ["Start"] + [f"D{d}" for d in days]
        assignment = dict(zip(var_names, vals))

        # Helper to get presence and counts
        counts = {c: 0 for c in cities}
        transitions = 0

        # Count city-day presence including flight days counting for prev city
        for d in days:
            curr = assignment[f"D{d}"]
            prev = assignment["Start"] if d == 1 else assignment[f"D{d-1}"]

            # Always present in the current city's day
            counts[curr] += 1

            # If a flight occurs on day d, count presence for previous city as well
            if curr != prev:
                transitions += 1
                # Check direct flight exists (also enforced locally for d>=2, but ensure for d==1)
                if d == 1:
                    # Start == D1 per earlier constraint, so this path won't happen
                    pass
                else:
                    if frozenset({prev, curr}) not in edges:
                        return False
                counts[prev] += 1

        # Durations must match exactly
        for c in cities:
            if counts[c] != durations[c]:
                return False

        # Exactly 4 travel days
        if transitions != 4:
            return False

        return True

    problem.addConstraint(global_constraint, ["Start"] + [f"D{d}" for d in days])

    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"itinerary": []}))
        return

    # Build itinerary as contiguous ranges of the main city per day
    day_cities = [solution[f"D{d}"] for d in days]

    itinerary = []
    start_day = 1
    current_city = day_cities[0]
    for d in range(2, total_days + 1):
        if day_cities[d - 1] != current_city:
            itinerary.append({"day_range": f"Day {start_day}-{d-1}", "place": current_city})
            start_day = d
            current_city = day_cities[d - 1]
    # Append last segment
    itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
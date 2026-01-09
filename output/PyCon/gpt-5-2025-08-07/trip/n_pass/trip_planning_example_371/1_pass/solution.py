import json
from constraint import Problem

def main():
    # Define cities and constraints
    cities = ["Vienna", "Stockholm", "Nice", "Split"]

    # Required days present in each city (including flight-day double presence)
    required_presence = {
        "Vienna": 2,
        "Stockholm": 5,
        "Nice": 2,
        "Split": 3,
    }

    total_days = 9
    # Number of flight days required so that sum of per-city days matches
    required_flights = sum(required_presence.values()) - total_days
    if required_flights < 0:
        # Impossible target if negative, but we keep going to let solver fail gracefully
        pass

    # Must-be-in-city constraints (presence on those days)
    must_be_present = {
        1: {"Vienna"},
        2: {"Vienna"},
        7: {"Split"},
        9: {"Split"},
    }

    # Allowed direct routes (undirected)
    direct_pairs = {
        frozenset(("Vienna", "Stockholm")),
        frozenset(("Vienna", "Nice")),
        frozenset(("Vienna", "Split")),
        frozenset(("Stockholm", "Split")),
        frozenset(("Nice", "Stockholm")),
    }

    # Set up the CSP
    problem = Problem()
    day_vars = [f"D{d}" for d in range(1, total_days + 1)]
    for var in day_vars:
        problem.addVariable(var, cities)

    # Day 1 must be Vienna to satisfy workshop presence on day 1 (no prior day to create presence via flight)
    problem.addConstraint(lambda d1: d1 == "Vienna", ("D1",))
    # Ensure we depart Vienna on Day 2 (otherwise any later departure would add an extra presence day for Vienna)
    problem.addConstraint(lambda d1, d2: d2 != d1, ("D1", "D2"))

    def global_constraint(*assignments):
        # Map day index to city for convenience
        day_city = {d: assignments[d - 1] for d in range(1, total_days + 1)}

        # Direct flight constraint, and count flights (transitions)
        flights = 0
        for d in range(2, total_days + 1):
            prev_c = day_city[d - 1]
            cur_c = day_city[d]
            if prev_c != cur_c:
                flights += 1
                if frozenset((prev_c, cur_c)) not in direct_pairs:
                    return False

        # Enforce required number of flights
        if flights != required_flights:
            return False

        # Compute presence per city and per day
        # Presence on day d includes:
        # - the current city's day_city[d]
        # - plus, if there is a flight that day (i.e., day_city[d-1] != day_city[d]), the previous city day_city[d-1]
        presence_counts = {c: 0 for c in cities}
        # Also enforce must-be-present constraints
        for d in range(1, total_days + 1):
            current = day_city[d]
            previous = day_city[d - 1] if d > 1 else None
            present_today = set()
            present_today.add(current)
            if d > 1 and previous != current:
                present_today.add(previous)

            # Must-be-present constraints
            if d in must_be_present:
                if not must_be_present[d].issubset(present_today):
                    return False

            for c in present_today:
                presence_counts[c] += 1

        # Enforce exact presence counts per city
        for c, req in required_presence.items():
            if presence_counts.get(c, 0) != req:
                return False

        return True

    problem.addConstraint(global_constraint, tuple(day_vars))

    solution = problem.getSolution()

    # Build output itinerary (day ranges for base city day_city[d])
    output = {"itinerary": []}
    if solution:
        # Construct ordered list of base cities by day
        base = [solution[f"D{d}"] for d in range(1, total_days + 1)]

        # Merge contiguous equal cities into ranges
        start = 1
        current_city = base[0]
        for d in range(2, total_days + 1):
            if base[d - 1] != current_city:
                output["itinerary"].append({
                    "day_range": f"Day {start}-{d-1}",
                    "place": current_city
                })
                start = d
                current_city = base[d - 1]
        # Add final segment
        output["itinerary"].append({
            "day_range": f"Day {start}-{total_days}",
            "place": current_city
        })

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()
import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables (trip constraints)
    total_days = 16
    cities = ["Mykonos", "Nice", "London", "Copenhagen", "Oslo", "Tallinn"]
    desired_days = {
        "Mykonos": 4,
        "Nice": 3,
        "London": 2,
        "Copenhagen": 3,
        "Oslo": 5,
        "Tallinn": 4,
    }
    # Direct flights (undirected)
    direct_pairs = [
        ("London", "Copenhagen"),
        ("Copenhagen", "Tallinn"),
        ("Tallinn", "Oslo"),
        ("Mykonos", "London"),
        ("Oslo", "Nice"),
        ("London", "Nice"),
        ("Mykonos", "Nice"),
        ("London", "Oslo"),
        ("Copenhagen", "Nice"),
        ("Copenhagen", "Oslo"),
    ]
    direct_routes = set(frozenset(p) for p in direct_pairs)

    # Derived block lengths based on the "double-count on travel day" rule:
    # For the last city, length = desired_days[city]
    # For all other cities, length = desired_days[city] - 1
    # The conference constraints force Nice to be the last city (days 14 and 16 in Nice, and exactly 3 Nice days).
    last_city = "Nice"
    lengths_by_city = {}
    for c in cities:
        if c == last_city:
            lengths_by_city[c] = desired_days[c]
        else:
            lengths_by_city[c] = desired_days[c] - 1

    # Verify lengths sum to total days
    if sum(lengths_by_city.values()) != total_days:
        raise ValueError("Block lengths do not sum to total days. Check input constraints.")

    # Setup CSP
    problem = Problem()

    # Variables: pos_1..pos_6 (order of city blocks)
    for i in range(1, 6):
        problem.addVariable(f"pos_{i}", cities)
    # Last position fixed to Nice (conference days 14 and 16)
    problem.addVariable("pos_6", [last_city])

    # All positions must be a permutation of the 6 cities
    problem.addConstraint(AllDifferentConstraint(), [f"pos_{i}" for i in range(1, 7)])

    # Direct flight constraints between consecutive blocks
    for i in range(1, 6):
        def edge_ok(a, b, routes=direct_routes):
            return frozenset((a, b)) in routes
        problem.addConstraint(edge_ok, (f"pos_{i}", f"pos_{i+1}"))

    # Global constraints: counts, conference days, friend meeting window
    def global_constraints(p1, p2, p3, p4, p5, p6):
        order = [p1, p2, p3, p4, p5, p6]

        # Build day-to-city mapping using block lengths
        day_to_city = {}
        day = 1
        for city in order:
            L = lengths_by_city[city]
            for d in range(day, day + L):
                day_to_city[d] = city
            day += L

        # Sanity: Cover exactly total_days
        if len(day_to_city) != total_days:
            return False

        # Conference days: must be in Nice on Day 14 and Day 16
        if day_to_city[14] != "Nice" or day_to_city[16] != "Nice":
            return False

        # Compute counts per city with the travel-day double-count rule
        counts = {c: 0 for c in cities}
        for d in range(1, total_days + 1):
            counts[day_to_city[d]] += 1
        transitions = 0
        for d in range(2, total_days + 1):
            if day_to_city[d] != day_to_city[d - 1]:
                transitions += 1
                counts[day_to_city[d - 1]] += 1  # origin city also counts on travel day

        # Must have exactly 5 transitions (since sum(desired)=21 = 16 + transitions)
        if transitions != 5:
            return False

        # Counts must match desired days exactly
        if counts != desired_days:
            return False

        # Friend meeting in Oslo between Day 10 and Day 14 (inclusive).
        # Being in Oslo on a travel day counts as being in Oslo.
        friend_ok = False
        for d in range(10, 15):
            in_oslo_today = (day_to_city[d] == "Oslo")
            leaving_from_oslo_today = (d > 1 and day_to_city[d - 1] == "Oslo" and day_to_city[d] != day_to_city[d - 1])
            if in_oslo_today or leaving_from_oslo_today:
                friend_ok = True
                break
        if not friend_ok:
            return False

        return True

    problem.addConstraint(
        global_constraints,
        tuple(f"pos_{i}" for i in range(1, 7))
    )

    # Solve
    solutions = problem.getSolutions()

    if not solutions:
        # No solution found; output an empty itinerary (still valid JSON)
        print(json.dumps({"itinerary": []}))
        return

    # Choose the first solution
    sol = solutions[0]
    order = [sol[f"pos_{i}"] for i in range(1, 7)]

    # Build itinerary with day ranges
    itinerary = []
    day = 1
    for city in order:
        L = lengths_by_city[city]
        itinerary.append({
            "day_range": f"Day {day}-{day + L - 1}",
            "place": city
        })
        day += L

    # Output result
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
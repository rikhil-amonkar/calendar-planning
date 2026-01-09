import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables and constraints
    total_days = 10
    cities = ["London", "Santorini", "Istanbul"]
    desired_stays = {"London": 3, "Santorini": 6, "Istanbul": 3}
    conference_days_in_santorini = [5, 10]
    # Direct flights (both directions)
    direct_flights = {
        ("Istanbul", "London"), ("London", "Istanbul"),
        ("London", "Santorini"), ("Santorini", "London")
    }

    # Setup constraint problem
    problem = Problem()

    # Order of visiting the three cities (3 segments)
    problem.addVariables(["C1", "C2", "C3"], cities)
    problem.addConstraint(AllDifferentConstraint(), ["C1", "C2", "C3"])

    # Length of stay in each segment
    # Stays must be positive and not exceed total days
    problem.addVariables(["L1", "L2", "L3"], range(1, total_days + 1))

    def itinerary_constraint(c1, c2, c3, l1, l2, l3):
        # Segment lengths must match desired stays for the respective cities
        if l1 != desired_stays[c1] or l2 != desired_stays[c2] or l3 != desired_stays[c3]:
            return False

        # Enforce direct flights between consecutive cities
        if (c1, c2) not in direct_flights or (c2, c3) not in direct_flights:
            return False

        # Calculate timeline with overlapping flight days
        end1 = l1
        start2 = end1
        end2 = end1 + l2 - 1
        start3 = end2
        end3 = end2 + l3 - 1

        # Ensure total unique days equals total_days
        if end3 != total_days:
            return False

        # Determine Santorini segment start and end
        if c1 == "Santorini":
            s_start, s_end = 1, end1
        elif c2 == "Santorini":
            s_start, s_end = start2, end2
        elif c3 == "Santorini":
            s_start, s_end = start3, end3
        else:
            return False

        # Conference days must be within Santorini segment
        for d in conference_days_in_santorini:
            if not (s_start <= d <= s_end):
                return False

        return True

    problem.addConstraint(itinerary_constraint, ["C1", "C2", "C3", "L1", "L2", "L3"])

    solutions = problem.getSolutions()

    if not solutions:
        print(json.dumps({"itinerary": []}))
        return

    # Select one solution (any optimal solution that satisfies constraints)
    sol = solutions[0]
    c1, c2, c3 = sol["C1"], sol["C2"], sol["C3"]
    l1, l2, l3 = sol["L1"], sol["L2"], sol["L3"]

    # Compute day ranges with overlaps for flights
    end1 = l1
    start2 = end1
    end2 = end1 + l2 - 1
    start3 = end2
    end3 = end2 + l3 - 1

    itinerary = [
        {"day_range": f"Day 1-{end1}", "place": c1},
        {"day_range": f"Day {start2}-{end2}", "place": c2},
        {"day_range": f"Day {start3}-{end3}", "place": c3},
    ]

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))


if __name__ == "__main__":
    main()
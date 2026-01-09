import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Trip parameters
    total_days = 19
    cities = ["Warsaw", "Copenhagen", "Stuttgart", "Bucharest", "Dubrovnik"]
    desired_days = {
        "Dubrovnik": 5,
        "Warsaw": 2,
        "Stuttgart": 7,
        "Bucharest": 6,
        "Copenhagen": 3,
    }
    # Direct flights (undirected)
    direct_flights = {
        frozenset(("Warsaw", "Copenhagen")),
        frozenset(("Stuttgart", "Copenhagen")),
        frozenset(("Warsaw", "Stuttgart")),
        frozenset(("Bucharest", "Copenhagen")),
        frozenset(("Bucharest", "Warsaw")),
        frozenset(("Copenhagen", "Dubrovnik")),
    }
    # Special constraints
    conference_days_in_stuttgart = [7, 13]
    wedding_window = (1, 6)  # inclusive day range for Bucharest presence

    # Set up CSP
    problem = Problem()

    # Position variables: each city gets a unique position 1..5 in the visit order
    for city in cities:
        problem.addVariable(f"P_{city}", [1, 2, 3, 4, 5])
    problem.addConstraint(AllDifferentConstraint(), [f"P_{city}" for city in cities])

    # Flight days (transition days between consecutive cities): t2 < t3 < t4 < t5
    # Domain restricted to [2..18] to ensure valid ranges for inclusive intervals
    problem.addVariable("t2", list(range(2, total_days)))
    problem.addVariable("t3", list(range(3, total_days)))
    problem.addVariable("t4", list(range(4, total_days)))
    problem.addVariable("t5", list(range(5, total_days)))
    problem.addConstraint(lambda t2, t3, t4, t5: t2 < t3 < t4 < t5 < total_days,
                          ("t2", "t3", "t4", "t5"))

    def itinerary_constraint(P_Warsaw, P_Copenhagen, P_Stuttgart, P_Bucharest, P_Dubrovnik, t2, t3, t4, t5):
        # Build position -> city and ordered list by positions 1..5
        pos_to_city = {
            P_Warsaw: "Warsaw",
            P_Copenhagen: "Copenhagen",
            P_Stuttgart: "Stuttgart",
            P_Bucharest: "Bucharest",
            P_Dubrovnik: "Dubrovnik",
        }
        order = [pos_to_city[i] for i in range(1, 6)]

        # Enforce direct flights for consecutive cities
        for i in range(4):
            if frozenset((order[i], order[i+1])) not in direct_flights:
                return False

        # Build city intervals based on flight days:
        # pos1: [1, t2], pos2: [t2, t3], pos3: [t3, t4], pos4: [t4, t5], pos5: [t5, total_days]
        intervals_by_pos = {
            1: (1, t2),
            2: (t2, t3),
            3: (t3, t4),
            4: (t4, t5),
            5: (t5, total_days),
        }
        # Validate durations for each city's assigned position
        for pos in range(1, 6):
            city = pos_to_city[pos]
            start, end = intervals_by_pos[pos]
            # Valid interval
            if not (1 <= start <= end <= total_days):
                return False
            length = end - start + 1
            if length != desired_days[city]:
                return False

        # Stuttgart must include both day 7 and day 13
        pos_stu = P_Stuttgart
        s_start, s_end = intervals_by_pos[pos_stu]
        if not (s_start <= 7 <= s_end and s_start <= 13 <= s_end):
            return False

        # Bucharest must overlap with wedding window [1,6]
        pos_b = P_Bucharest
        b_start, b_end = intervals_by_pos[pos_b]
        if not (max(b_start, wedding_window[0]) <= min(b_end, wedding_window[1])):
            return False

        return True

    problem.addConstraint(
        itinerary_constraint,
        (
            "P_Warsaw",
            "P_Copenhagen",
            "P_Stuttgart",
            "P_Bucharest",
            "P_Dubrovnik",
            "t2",
            "t3",
            "t4",
            "t5",
        ),
    )

    solutions = problem.getSolutions()

    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return

    # Choose the first solution deterministically by sorting for readability
    # Sort by (P_Bucharest, P_Warsaw, P_Stuttgart, P_Copenhagen, P_Dubrovnik, t2, t3, t4, t5)
    def sol_key(sol):
        return (
            sol["P_Bucharest"],
            sol["P_Warsaw"],
            sol["P_Stuttgart"],
            sol["P_Copenhagen"],
            sol["P_Dubrovnik"],
            sol["t2"],
            sol["t3"],
            sol["t4"],
            sol["t5"],
        )

    sol = sorted(solutions, key=sol_key)[0]

    # Reconstruct order and intervals
    pos_to_city = {
        sol["P_Warsaw"]: "Warsaw",
        sol["P_Copenhagen"]: "Copenhagen",
        sol["P_Stuttgart"]: "Stuttgart",
        sol["P_Bucharest"]: "Bucharest",
        sol["P_Dubrovnik"]: "Dubrovnik",
    }
    order = [pos_to_city[i] for i in range(1, 6)]
    t2, t3, t4, t5 = sol["t2"], sol["t3"], sol["t4"], sol["t5"]
    intervals_by_pos = {
        1: (1, t2),
        2: (t2, t3),
        3: (t3, t4),
        4: (t4, t5),
        5: (t5, total_days),
    }

    itinerary = []
    for i in range(1, 6):
        start, end = intervals_by_pos[i]
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": order[i - 1]
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
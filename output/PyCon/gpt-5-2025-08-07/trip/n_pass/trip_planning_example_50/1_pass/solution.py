import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input constraints
    trip_length = 12
    cities = ["Vilnius", "Munich", "Mykonos"]
    desired_days = {
        "Vilnius": 4,
        "Munich": 3,
        "Mykonos": 7,
    }
    # Direct flights: treat "Munich and Mykonos" as bidirectional; "from Vilnius to Munich" as directed
    direct_flights = {
        ("Munich", "Mykonos"),
        ("Mykonos", "Munich"),
        ("Vilnius", "Munich"),
    }

    # Set up CSP
    problem = Problem()

    # Variables: order of visiting the 3 cities (start, middle, end)
    problem.addVariables(["start", "middle", "end"], cities)
    problem.addConstraint(AllDifferentConstraint(), ["start", "middle", "end"])

    # Flight days between city1->city2 and city2->city3
    # d1 is the day we fly from start to middle; d2 is the day we fly from middle to end
    problem.addVariable("d1", range(1, trip_length + 1))
    problem.addVariable("d2", range(1, trip_length + 1))

    # Enforce direct flights for both legs
    def direct_edge_constraint(start, middle, end):
        return (start, middle) in direct_flights and (middle, end) in direct_flights
    problem.addConstraint(direct_edge_constraint, ["start", "middle", "end"])

    # Enforce chronological flight order and valid bounds
    def flight_day_order(d1, d2):
        return 1 <= d1 < d2 <= trip_length
    problem.addConstraint(flight_day_order, ["d1", "d2"])

    # City-day counting rule:
    # - Day 1..(d1-1): start city only
    # - Day d1: both start and middle
    # - Day (d1+1)..(d2-1): middle only
    # - Day d2: both middle and end
    # - Day (d2+1)..trip_length: end only
    def duration_match_constraint(start, middle, end, d1, d2):
        # computed city-days based on flight days
        counts = {
            start: d1,
            middle: (d2 - d1 + 1),
            end: (trip_length + 1 - d2),
        }
        # Ensure counts match desired_days exactly for all three cities
        for c in cities:
            if counts.get(c, 0) != desired_days[c]:
                return False
        return True

    problem.addConstraint(duration_match_constraint, ["start", "middle", "end", "d1", "d2"])

    # Solve
    solutions = problem.getSolutions()

    itinerary_output = {"itinerary": []}

    if solutions:
        # Choose a solution deterministically (earliest d1, then earliest d2)
        solutions.sort(key=lambda s: (s["d1"], s["d2"], s["start"], s["middle"], s["end"]))
        sol = solutions[0]
        start, middle, end = sol["start"], sol["middle"], sol["end"]
        d1, d2 = sol["d1"], sol["d2"]

        # Build itinerary with overlapping day boundaries on flight days
        itinerary_output["itinerary"] = [
            {"day_range": f"Day 1-{d1}", "place": start},
            {"day_range": f"Day {d1}-{d2}", "place": middle},
            {"day_range": f"Day {d2}-{trip_length}", "place": end},
        ]

    print(json.dumps(itinerary_output, ensure_ascii=False))

if __name__ == "__main__":
    main()
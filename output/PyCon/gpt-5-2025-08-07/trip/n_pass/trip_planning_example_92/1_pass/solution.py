import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables (trip constraints)
    total_days = 12
    city_stays = {
        "Riga": 5,
        "Vilnius": 7,
        "Dublin": 2
    }
    cities = list(city_stays.keys())
    # Direct flights: bidirectional between Dublin and Riga; one-way from Riga to Vilnius
    direct_flights = {
        ("Dublin", "Riga"),
        ("Riga", "Dublin"),
        ("Riga", "Vilnius"),
    }

    # Set up constraint problem
    problem = Problem()

    # Variables for the order of cities visited
    problem.addVariables(("C1", "C2", "C3"), cities)
    problem.addConstraint(AllDifferentConstraint(), ("C1", "C2", "C3"))

    # Enforce direct flights between consecutive cities
    problem.addConstraint(lambda a, b: (a, b) in direct_flights, ("C1", "C2"))
    problem.addConstraint(lambda a, b: (a, b) in direct_flights, ("C2", "C3"))

    # Variables for start days of each city segment
    # Trip starts on Day 1
    problem.addVariable("S1", [1])
    problem.addVariables(("S2", "S3"), range(1, total_days + 1))

    # Overlap-by-one-day constraints at transitions:
    # S2 == end of first city's block = S1 + stay(C1) - 1
    problem.addConstraint(
        lambda s1, c1, s2, stays=city_stays: s2 == s1 + stays[c1] - 1,
        ("S1", "C1", "S2")
    )
    # S3 == end of second city's block = S2 + stay(C2) - 1
    problem.addConstraint(
        lambda s2, c2, s3, stays=city_stays: s3 == s2 + stays[c2] - 1,
        ("S2", "C2", "S3")
    )
    # The itinerary must end on total_days: end of third city = S3 + stay(C3) - 1 == total_days
    problem.addConstraint(
        lambda s3, c3, total=total_days, stays=city_stays: s3 + stays[c3] - 1 == total,
        ("S3", "C3")
    )

    # Solve
    solutions = problem.getSolutions()

    itinerary = []
    if solutions:
        # Choose one solution deterministically (e.g., first)
        sol = solutions[0]

        segments = [
            (sol["S1"], sol["C1"], city_stays[sol["C1"]]),
            (sol["S2"], sol["C2"], city_stays[sol["C2"]]),
            (sol["S3"], sol["C3"], city_stays[sol["C3"]]),
        ]
        # Sort by start day to ensure chronological order
        segments.sort(key=lambda x: x[0])

        for start, place, dur in segments:
            end = start + dur - 1
            itinerary.append({
                "day_range": f"Day {start}-{end}",
                "place": place
            })
    else:
        itinerary = []

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
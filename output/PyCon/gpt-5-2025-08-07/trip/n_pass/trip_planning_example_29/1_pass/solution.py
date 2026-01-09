import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables (trip constraints)
    total_days = 10
    cities = ["Krakow", "Dubrovnik", "Frankfurt"]
    durations = {"Krakow": 2, "Dubrovnik": 7, "Frankfurt": 3}
    # Undirected direct flights represented as directed pairs for adjacency checks
    direct_flights = {
        ("Frankfurt", "Krakow"), ("Krakow", "Frankfurt"),
        ("Dubrovnik", "Frankfurt"), ("Frankfurt", "Dubrovnik")
    }
    # Wedding must be in Krakow between Day 9 and Day 10
    wedding_city = "Krakow"
    wedding_days = (9, 10)

    # Set up CSP
    problem = Problem()
    problem.addVariables(["C1", "C2", "C3"], cities)
    problem.addConstraint(AllDifferentConstraint(), ["C1", "C2", "C3"])

    # Enforce direct flights adjacency
    def adjacency_ok(c1, c2, c3):
        return (c1, c2) in direct_flights and (c2, c3) in direct_flights
    problem.addConstraint(adjacency_ok, ["C1", "C2", "C3"])

    # Transition days between city segments (inclusive ranges; overlap on flight days)
    problem.addVariables(["t1", "t2"], range(1, total_days + 1))

    # Timing and duration constraints linking city order and transition days
    def timing_ok(c1, c2, c3, t1, t2):
        if not (1 <= t1 <= t2 <= total_days):
            return False
        l1 = t1                       # Days in first city: Day 1..t1
        l2 = t2 - t1 + 1              # Days in second city: Day t1..t2
        l3 = (total_days + 1) - t2    # Days in third city: Day t2..total_days
        return durations[c1] == l1 and durations[c2] == l2 and durations[c3] == l3
    problem.addConstraint(timing_ok, ["C1", "C2", "C3", "t1", "t2"])

    # Wedding constraint: must be in Krakow on Day 10 (and Day 9 follows from durations)
    problem.addConstraint(lambda c3: c3 == wedding_city, ["C3"])

    # Solve
    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"itinerary": []}))
        return

    # Build itinerary with overlapping day ranges on flight days
    c1, c2, c3 = solution["C1"], solution["C2"], solution["C3"]
    t1, t2 = solution["t1"], solution["t2"]

    itinerary = [
        {"day_range": f"Day 1-{t1}", "place": c1},
        {"day_range": f"Day {t1}-{t2}", "place": c2},
        {"day_range": f"Day {t2}-{total_days}", "place": c3},
    ]

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
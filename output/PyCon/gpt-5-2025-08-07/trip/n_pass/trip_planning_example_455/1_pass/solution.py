import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables / constraints
    total_days = 21
    cities = ["Reykjavik", "Riga", "Warsaw", "Istanbul", "Krakow"]
    durations = {
        "Reykjavik": 7,
        "Riga": 2,
        "Warsaw": 3,
        "Istanbul": 6,
        "Krakow": 7
    }
    # Direct flights (undirected)
    direct_flights = {
        frozenset(("Istanbul", "Krakow")),
        frozenset(("Warsaw", "Reykjavik")),
        frozenset(("Istanbul", "Warsaw")),
        frozenset(("Riga", "Istanbul")),
        frozenset(("Krakow", "Warsaw")),
        frozenset(("Riga", "Warsaw")),
    }

    # Set up CSP
    problem = Problem()

    # Variables: Order O1..O5 (cities), Starts S1..S5, Ends E1..E5
    order_vars = [f"O{i}" for i in range(1, 6)]
    start_vars = [f"S{i}" for i in range(1, 6)]
    end_vars = [f"E{i}" for i in range(1, 6)]

    # Domains
    for var in order_vars:
        problem.addVariable(var, cities)
    for var in start_vars + end_vars:
        problem.addVariable(var, range(1, total_days + 1))

    # All cities visited exactly once
    problem.addConstraint(AllDifferentConstraint(), order_vars)

    # Start at Day 1 and end on Day 21
    problem.addConstraint(lambda s1: s1 == 1, ("S1",))
    problem.addConstraint(lambda e5: e5 == total_days, ("E5",))

    # Duration constraints: Ei = Si + duration(city) - 1
    def duration_constraint(city, s, e):
        return e - s + 1 == durations[city]
    for i in range(1, 6):
        problem.addConstraint(duration_constraint, (f"O{i}", f"S{i}", f"E{i}"))

    # Transition constraints: S(i+1) = E(i) (flying day counted in both cities)
    for i in range(1, 5):
        problem.addConstraint(lambda e, s_next: s_next == e, (f"E{i}", f"S{i+1}"))

    # Direct flight constraints between consecutive cities
    def direct_flight_constraint(a, b):
        return frozenset((a, b)) in direct_flights
    for i in range(1, 5):
        problem.addConstraint(direct_flight_constraint, (f"O{i}", f"O{i+1}"))

    # Special constraints:
    # - Meet friend in Riga between day 1 and day 2 (inclusive): [S_Riga, E_Riga] intersects {1,2}
    # - Attend wedding in Istanbul between day 2 and day 7 (inclusive): [S_Istanbul, E_Istanbul] intersects [2,7]
    def special_constraints(
        O1, S1, E1,
        O2, S2, E2,
        O3, S3, E3,
        O4, S4, E4,
        O5, S5, E5
    ):
        tuples = [(O1, S1, E1), (O2, S2, E2), (O3, S3, E3), (O4, S4, E4), (O5, S5, E5)]

        # Find Riga and Istanbul segments
        riga_seg = next(((s, e) for (o, s, e) in tuples if o == "Riga"), None)
        istanbul_seg = next(((s, e) for (o, s, e) in tuples if o == "Istanbul"), None)

        if riga_seg is None or istanbul_seg is None:
            return False

        s_riga, e_riga = riga_seg
        s_ist, e_ist = istanbul_seg

        # Riga overlaps day 1 or 2
        riga_ok = (s_riga <= 2) and (e_riga >= 1)

        # Istanbul overlaps days 2..7
        ist_ok = (s_ist <= 7) and (e_ist >= 2)

        return riga_ok and ist_ok

    problem.addConstraint(
        special_constraints,
        (
            "O1", "S1", "E1",
            "O2", "S2", "E2",
            "O3", "S3", "E3",
            "O4", "S4", "E4",
            "O5", "S5", "E5",
        )
    )

    solutions = problem.getSolutions()

    if not solutions:
        print(json.dumps({"itinerary": [], "error": "No feasible itinerary found with given constraints"}))
        return

    # Choose a solution deterministically: sort by (S1, S2, S3, S4, S5, O1..O5) and pick first
    def sol_key(sol):
        return tuple([sol[f"S{i}"] for i in range(1, 6)] + [sol[f"O{i}"] for i in range(1, 6)])
    solutions.sort(key=sol_key)
    sol = solutions[0]

    # Build itinerary list sorted by start day
    segments = []
    for i in range(1, 6):
        city = sol[f"O{i}"]
        s = sol[f"S{i}"]
        e = sol[f"E{i}"]
        segments.append((s, e, city))
    segments.sort(key=lambda x: x[0])

    itinerary = []
    for s, e, city in segments:
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables and constraints
    total_days = 16
    cities = ["Dubrovnik", "Split", "Milan", "Porto", "Krakow", "Munich"]

    # Desired stays per city (inclusive of flight day overlaps as specified)
    desired_days = {
        "Dubrovnik": 4,
        "Split": 3,
        "Milan": 3,
        "Porto": 4,
        "Krakow": 2,
        "Munich": 5,
    }

    # Special time windows (inclusive):
    # - Must be in Munich on days 4-8 (5 days)
    # - Must be in Krakow on days 8-9 (2 days)
    # - Must be in Milan overlapping with days 11-13 at least one day
    munich_window = (4, 8)
    krakow_window = (8, 9)
    milan_window = (11, 13)

    # Direct flights (undirected)
    flight_pairs = [
        ("Munich", "Porto"),
        ("Split", "Milan"),
        ("Milan", "Porto"),
        ("Munich", "Krakow"),
        ("Munich", "Milan"),
        ("Dubrovnik", "Munich"),
        ("Krakow", "Split"),
        ("Krakow", "Milan"),
        ("Munich", "Split"),
    ]
    direct_flights = set(frozenset(pair) for pair in flight_pairs)

    # Build constraint problem
    problem = Problem()

    # Sequence positions for cities
    pos_vars = [f"pos{i}" for i in range(1, 7)]
    problem.addVariables(pos_vars, cities)
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Start and end day variables per position
    start_vars = [f"S{i}" for i in range(1, 7)]
    end_vars = [f"E{i}" for i in range(1, 7)]
    for s in start_vars + end_vars:
        problem.addVariable(s, range(1, total_days + 1))

    # Duration constraints per position dependent on which city is at that position
    for i in range(6):
        pvar = pos_vars[i]
        svar = start_vars[i]
        evar = end_vars[i]

        def duration_constraint(city, s, e, dd=desired_days):
            return (e - s + 1) == dd[city]
        problem.addConstraint(duration_constraint, [pvar, svar, evar])

        # Special window constraints
        def special_windows(city, s, e, mw=munich_window, kw=krakow_window, milw=milan_window):
            if city == "Munich":
                return s == mw[0] and e == mw[1]
            if city == "Krakow":
                return s == kw[0] and e == kw[1]
            if city == "Milan":
                # Overlap Milan with [11, 13] at least one day
                return not (e < milw[0] or s > milw[1])
            return True
        problem.addConstraint(special_windows, [pvar, svar, evar])

    # Adjacency and direct flight constraints
    for i in range(5):
        s_next = start_vars[i + 1]
        e_cur = end_vars[i]
        p_cur = pos_vars[i]
        p_next = pos_vars[i + 1]

        # Flight day overlap: if flying from city A to B on day X,
        # you are in both A and B on day X => S_{i+1} == E_{i}
        problem.addConstraint(lambda s2, e1: s2 == e1, [s_next, e_cur])

        # Only allow direct flights between consecutive cities
        def flight_constraint(c1, c2, flights=direct_flights):
            return frozenset([c1, c2]) in flights
        problem.addConstraint(flight_constraint, [p_cur, p_next])

    # Start day and end day constraints
    problem.addConstraint(lambda s1: s1 == 1, [start_vars[0]])
    problem.addConstraint(lambda e6: e6 == total_days, [end_vars[-1]])

    # Solve
    solutions = problem.getSolutions()

    if not solutions:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    # Choose the first solution
    sol = solutions[0]

    # Build itinerary in sequence order
    itinerary = []
    for i in range(6):
        city = sol[pos_vars[i]]
        s = sol[start_vars[i]]
        e = sol[end_vars[i]]
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
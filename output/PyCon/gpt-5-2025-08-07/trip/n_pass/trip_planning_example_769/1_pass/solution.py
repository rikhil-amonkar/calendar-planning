import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables / constraints
    total_days = 16
    cities = ["Porto", "Prague", "Reykjavik", "Santorini", "Amsterdam", "Munich"]
    durations = {
        "Porto": 5,
        "Prague": 4,
        "Reykjavik": 4,
        "Santorini": 2,
        "Amsterdam": 2,
        "Munich": 4,
    }
    # Direct flights (undirected)
    direct_pairs = [
        ("Porto", "Amsterdam"),
        ("Munich", "Amsterdam"),
        ("Reykjavik", "Amsterdam"),
        ("Munich", "Porto"),
        ("Prague", "Reykjavik"),
        ("Reykjavik", "Munich"),
        ("Amsterdam", "Santorini"),
        ("Prague", "Amsterdam"),
        ("Prague", "Munich"),
    ]
    flights = set(frozenset(pair) for pair in direct_pairs)

    # Build CSP
    problem = Problem()

    # Variables: City at each position (1..6), Start and End days for each position
    positions = range(1, 7)

    # Each position has a city
    for p in positions:
        problem.addVariable(f"City{p}", cities)

    # All cities must be different and exactly the set we have
    problem.addConstraint(AllDifferentConstraint(), [f"City{p}" for p in positions])

    # Start and End days
    for p in positions:
        problem.addVariable(f"S{p}", range(1, total_days + 1))
        problem.addVariable(f"E{p}", range(1, total_days + 1))

    # Duration constraints: E - S + 1 == duration(City)
    for p in positions:
        problem.addConstraint(
            lambda c, s, e, durations=durations: e - s + 1 == durations[c],
            (f"City{p}", f"S{p}", f"E{p}")
        )

    # Chain constraints:
    # Start on Day 1
    problem.addConstraint(lambda s1: s1 == 1, ("S1",))
    # Overlap-by-one rule for transitions: S_{p+1} == E_p
    for p in range(1, 6):
        problem.addConstraint(
            lambda s_next, e_prev: s_next == e_prev,
            (f"S{p+1}", f"E{p}")
        )
    # End on Day 16
    problem.addConstraint(lambda e6: e6 == total_days, ("E6",))

    # Direct flight constraints between consecutive cities
    for p in range(1, 6):
        problem.addConstraint(
            lambda c1, c2, flights=flights: frozenset((c1, c2)) in flights,
            (f"City{p}", f"City{p+1}")
        )

    # Event/window constraints:
    # Reykjavik wedding between day 4 and 7: must overlap that window
    for p in positions:
        problem.addConstraint(
            lambda c, s, e: (c != "Reykjavik") or (e >= 4 and s <= 7),
            (f"City{p}", f"S{p}", f"E{p}")
        )
    # Amsterdam conference on day 14 and 15: both days must be covered
    for p in positions:
        problem.addConstraint(
            lambda c, s, e: (c != "Amsterdam") or (s <= 14 and e >= 15),
            (f"City{p}", f"S{p}", f"E{p}")
        )
    # Meet friend in Munich between day 7 and 10: overlap that window
    for p in positions:
        problem.addConstraint(
            lambda c, s, e: (c != "Munich") or (e >= 7 and s <= 10),
            (f"City{p}", f"S{p}", f"E{p}")
        )

    # Solve
    solutions = problem.getSolutions()

    itinerary = []
    if solutions:
        # Choose a deterministic solution by sorting solutions by the tuple of (S1,S2,...,S6, City1,..City6)
        def sol_key(sol):
            return tuple([sol[f"S{p}"] for p in positions] + [sol[f"City{p}"] for p in positions])
        sol = sorted(solutions, key=sol_key)[0]

        # Build itinerary segments in order
        for p in positions:
            s = sol[f"S{p}"]
            e = sol[f"E{p}"]
            city = sol[f"City{p}"]
            itinerary.append({"day_range": f"Day {s}-{e}", "place": city})

    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()
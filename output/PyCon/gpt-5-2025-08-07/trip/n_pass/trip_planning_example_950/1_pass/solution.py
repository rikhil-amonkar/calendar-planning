import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and required stays (in days)
    cities = ["Rome", "Mykonos", "Nice", "Riga", "Bucharest", "Munich", "Krakow"]
    required_durations = {
        "Rome": 4,
        "Mykonos": 3,
        "Nice": 3,
        "Riga": 3,
        "Bucharest": 4,
        "Munich": 4,
        "Krakow": 2,
    }

    # Direct flights (edges). Undirected edges are added both ways; directed are one-way only.
    undirected_pairs = [
        ("Nice", "Riga"),
        ("Bucharest", "Munich"),
        ("Mykonos", "Munich"),
        ("Riga", "Bucharest"),
        ("Rome", "Nice"),
        ("Rome", "Munich"),
        ("Mykonos", "Nice"),
        ("Rome", "Mykonos"),
        ("Munich", "Krakow"),
        ("Rome", "Bucharest"),
        ("Nice", "Munich"),
    ]
    directed_pairs = [
        ("Riga", "Munich"),
        ("Rome", "Riga"),
    ]

    allowed_flights = set()
    for a, b in undirected_pairs:
        allowed_flights.add((a, b))
        allowed_flights.add((b, a))
    for a, b in directed_pairs:
        allowed_flights.add((a, b))

    # Create CSP
    problem = Problem()

    # Variables for 7 segments: city Ci, start Si, duration Di, end Ei
    C_vars = [f"C{i}" for i in range(7)]
    S_vars = [f"S{i}" for i in range(7)]
    D_vars = [f"D{i}" for i in range(7)]
    E_vars = [f"E{i}" for i in range(7)]

    # Domains
    for i in range(7):
        problem.addVariable(C_vars[i], cities)
        problem.addVariable(S_vars[i], range(1, 18))   # days 1..17
        problem.addVariable(E_vars[i], range(1, 18))
        # Durations can be one of the specified values; will be pinned by mapping constraint
        problem.addVariable(D_vars[i], list(set(required_durations.values())))

    # All cities must be used exactly once (a permutation of the 7 cities)
    problem.addConstraint(AllDifferentConstraint(), C_vars)

    # Link duration to the chosen city: Di == required_durations[Ci]
    for i in range(7):
        def dur_match(ci, di, req=required_durations):
            return di == req[ci]
        problem.addConstraint(dur_match, [C_vars[i], D_vars[i]])

    # Define end day: Ei = Si + Di - 1
    for i in range(7):
        problem.addConstraint(lambda s, d, e: e == s + d - 1, [S_vars[i], D_vars[i], E_vars[i]])

    # Sequential adjacency: Si == E(i-1)
    for i in range(1, 7):
        problem.addConstraint(lambda eprev, snext: eprev == snext, [E_vars[i-1], S_vars[i]])

    # Start on Day 1 and finish on Day 17
    problem.addConstraint(lambda s: s == 1, [S_vars[0]])
    problem.addConstraint(lambda e: e == 17, [E_vars[6]])

    # Flight feasibility between consecutive cities
    for i in range(1, 7):
        def flight_ok(prev_city, next_city, allowed=allowed_flights):
            return (prev_city, next_city) in allowed
        problem.addConstraint(flight_ok, [C_vars[i-1], C_vars[i]])

    # Special day constraints:
    # - Must be in Rome on day 1 and day 4
    # - Must be in Mykonos on days 4, 5, 6
    # - Must be in Krakow on days 16, 17
    for i in range(7):
        def special_days_ok(ci, s, e):
            # Rome: day 1 and day 4 must be within [s, e]
            if ci == "Rome":
                if not (s <= 1 <= e and s <= 4 <= e):
                    return False
            # Mykonos: days 4..6 must be within [s, e]
            if ci == "Mykonos":
                if not (s <= 4 and e >= 6):
                    return False
            # Krakow: days 16..17 must be within [s, e]
            if ci == "Krakow":
                if not (s <= 16 and e >= 17):
                    return False
            return True
        problem.addConstraint(special_days_ok, [C_vars[i], S_vars[i], E_vars[i]])

    # Solve
    solution = problem.getSolution()

    if not solution:
        print(json.dumps({"itinerary": []}))
        return

    # Build itinerary sorted by segment index (0..6)
    itinerary = []
    for i in range(7):
        city = solution[C_vars[i]]
        s = solution[S_vars[i]]
        e = solution[E_vars[i]]
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
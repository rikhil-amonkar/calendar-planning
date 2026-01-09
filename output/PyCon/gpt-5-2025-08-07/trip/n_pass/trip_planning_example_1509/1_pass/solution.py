import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Cities and durations (days counted include flight overlap days)
    cities = [
        "Paris", "Warsaw", "Krakow", "Tallinn", "Riga",
        "Copenhagen", "Helsinki", "Oslo", "Santorini", "Lyon"
    ]
    durations = {
        "Paris": 5,
        "Warsaw": 2,
        "Krakow": 2,
        "Tallinn": 2,
        "Riga": 2,
        "Copenhagen": 5,
        "Helsinki": 5,
        "Oslo": 5,
        "Santorini": 2,
        "Lyon": 4
    }

    # Build directed flight edges based on provided data
    # "A and B" means both directions, "from A to B" means one direction
    bidirectional_pairs = [
        ("Warsaw", "Riga"),
        ("Warsaw", "Tallinn"),
        ("Copenhagen", "Helsinki"),
        ("Lyon", "Paris"),
        ("Copenhagen", "Warsaw"),
        ("Lyon", "Oslo"),
        ("Paris", "Oslo"),
        ("Paris", "Riga"),
        ("Krakow", "Helsinki"),
        ("Paris", "Tallinn"),
        ("Oslo", "Riga"),
        ("Krakow", "Warsaw"),
        ("Paris", "Helsinki"),
        ("Copenhagen", "Santorini"),
        ("Helsinki", "Warsaw"),
        ("Helsinki", "Riga"),
        ("Copenhagen", "Krakow"),
        ("Copenhagen", "Riga"),
        ("Paris", "Krakow"),
        ("Copenhagen", "Oslo"),
        ("Oslo", "Tallinn"),
        ("Oslo", "Helsinki"),
        ("Copenhagen", "Tallinn"),
        ("Oslo", "Krakow"),
        ("Helsinki", "Tallinn"),
        ("Paris", "Copenhagen"),
        ("Paris", "Warsaw"),
        ("Oslo", "Warsaw"),
    ]
    directed_only = [
        ("Riga", "Tallinn"),
        ("Santorini", "Oslo")
    ]

    directed_edges = set()
    for a, b in bidirectional_pairs:
        directed_edges.add((a, b))
        directed_edges.add((b, a))
    for a, b in directed_only:
        directed_edges.add((a, b))

    # Problem setup
    problem = Problem()

    # Variables for positions 1..10 (sequence of cities)
    pos_vars = [f"city{i}" for i in range(1, 11)]
    problem.addVariables(pos_vars, cities)
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Start and end days for each position
    start_vars = [f"s{i}" for i in range(1, 11)]
    end_vars = [f"e{i}" for i in range(1, 11)]
    # Domain for days
    for v in start_vars + end_vars:
        problem.addVariable(v, range(1, 26))

    # s1 = 1, e10 = 25
    problem.addConstraint(lambda s: s == 1, (start_vars[0],))
    problem.addConstraint(lambda e: e == 25, (end_vars[-1],))

    # Duration constraints: e_i = s_i + durations[city_i] - 1
    def duration_constraint(city, s, e):
        return e == s + durations[city] - 1

    for i in range(10):
        problem.addConstraint(duration_constraint, (pos_vars[i], start_vars[i], end_vars[i]))

    # Chain constraints: s_{i+1} = e_i (overlap on flight day)
    for i in range(9):
        problem.addConstraint(lambda e_prev, s_next: s_next == e_prev, (end_vars[i], start_vars[i+1]))

    # Direct flight constraints for consecutive cities
    def flight_constraint(a, b):
        return (a, b) in directed_edges

    for i in range(9):
        problem.addConstraint(flight_constraint, (pos_vars[i], pos_vars[i+1]))

    # City-specific temporal constraints
    # Paris: include any day in [4, 8]
    def paris_window(city, s, e):
        if city != "Paris":
            return True
        return not (e < 4 or s > 8)

    # Krakow: must be days 17-18 exactly
    def krakow_exact(city, s, e):
        if city != "Krakow":
            return True
        return s == 17 and e == 18

    # Riga: must be days 23-24 exactly (wedding)
    def riga_exact(city, s, e):
        if city != "Riga":
            return True
        return s == 23 and e == 24

    # Santorini: must be days 12-13 exactly (relatives)
    def santorini_exact(city, s, e):
        if city != "Santorini":
            return True
        return s == 12 and e == 13

    # Helsinki: meet friend any day in [18, 22]
    def helsinki_window(city, s, e):
        if city != "Helsinki":
            return True
        return not (e < 18 or s > 22)

    for i in range(10):
        problem.addConstraint(paris_window, (pos_vars[i], start_vars[i], end_vars[i]))
        problem.addConstraint(krakow_exact, (pos_vars[i], start_vars[i], end_vars[i]))
        problem.addConstraint(riga_exact, (pos_vars[i], start_vars[i], end_vars[i]))
        problem.addConstraint(santorini_exact, (pos_vars[i], start_vars[i], end_vars[i]))
        problem.addConstraint(helsinki_window, (pos_vars[i], start_vars[i], end_vars[i]))

    solution = problem.getSolution()

    if not solution:
        # Fallback: no solution (should not happen with given constraints)
        print(json.dumps({"itinerary": []}))
        return

    # Build itinerary list ordered by start day
    segments = []
    for i in range(1, 11):
        city = solution[f"city{i}"]
        s = solution[f"s{i}"]
        e = solution[f"e{i}"]
        segments.append((s, e, city))

    segments.sort(key=lambda x: (x[0], x[1]))

    itinerary = []
    for s, e, city in segments:
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
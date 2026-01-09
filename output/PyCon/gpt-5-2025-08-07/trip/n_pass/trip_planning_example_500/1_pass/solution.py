import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define trip parameters
    total_days = 20
    cities = ["Hamburg", "Munich", "Manchester", "Lyon", "Split"]
    durations = {
        "Hamburg": 7,
        "Munich": 6,
        "Manchester": 2,
        "Lyon": 2,
        "Split": 7
    }
    # Special day constraints
    lyon_show_days = (13, 14)  # inclusive
    manchester_relatives_days = (19, 20)  # inclusive

    # Define direct flights (directed edges)
    undirected_edges = [
        ("Split", "Munich"),
        ("Munich", "Manchester"),
        ("Hamburg", "Manchester"),
        ("Hamburg", "Munich"),
        ("Split", "Lyon"),
        ("Lyon", "Munich"),
        ("Hamburg", "Split"),
    ]
    directed_edges = set()
    for a, b in undirected_edges:
        directed_edges.add((a, b))
        directed_edges.add((b, a))
    directed_edges.add(("Manchester", "Split"))  # explicitly directional

    # Set up constraint problem
    problem = Problem()

    # Variables: positions of cities in sequence
    pos_vars = [f"pos{i}" for i in range(1, 6)]
    for var in pos_vars:
        problem.addVariable(var, cities)
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Variables: start and end days for each segment (inclusive)
    s_vars = [f"s{i}" for i in range(1, 6)]
    e_vars = [f"e{i}" for i in range(1, 6)]
    for var in s_vars + e_vars:
        problem.addVariable(var, range(1, total_days + 1))

    # Global day bounds
    problem.addConstraint(lambda s: s == 1, ("s1",))
    problem.addConstraint(lambda e: e == total_days, ("e5",))

    # Consecutive segments overlap by one day (flight day counts for both cities)
    for i in range(1, 5):
        problem.addConstraint(lambda e_prev, s_next: e_prev == s_next, (f"e{i}", f"s{i+1}"))

    # Duration constraints for each segment based on the city assigned to that segment
    def duration_constraint(city, s, e):
        return (e - s + 1) == durations[city]

    for i in range(1, 6):
        problem.addConstraint(duration_constraint, (f"pos{i}", f"s{i}", f"e{i}"))

    # Direct flight constraints between consecutive cities
    def flight_constraint(city_a, city_b):
        return (city_a, city_b) in directed_edges

    for i in range(1, 5):
        problem.addConstraint(flight_constraint, (f"pos{i}", f"pos{i+1}"))

    # Special fixed-day constraints
    def lyon_constraint(city, s, e):
        if city == "Lyon":
            return s == lyon_show_days[0] and e == lyon_show_days[1]
        return True

    def manchester_constraint(city, s, e):
        if city == "Manchester":
            return s == manchester_relatives_days[0] and e == manchester_relatives_days[1]
        return True

    for i in range(1, 6):
        problem.addConstraint(lyon_constraint, (f"pos{i}", f"s{i}", f"e{i}"))
        problem.addConstraint(manchester_constraint, (f"pos{i}", f"s{i}", f"e{i}"))

    # Solve
    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"error": "No feasible itinerary found with given constraints"}))
        return

    # Build itinerary output
    itinerary = []
    for i in range(1, 6):
        s = solution[f"s{i}"]
        e = solution[f"e{i}"]
        city = solution[f"pos{i}"]
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
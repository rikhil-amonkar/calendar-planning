import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and required durations
    cities = [
        "Paris", "Barcelona", "Florence", "Tallinn", "Vilnius",
        "Warsaw", "Venice", "Amsterdam", "Hamburg", "Salzburg"
    ]
    durations = {
        "Paris": 2,
        "Barcelona": 5,
        "Florence": 5,
        "Tallinn": 2,
        "Vilnius": 3,
        "Warsaw": 4,
        "Venice": 3,
        "Amsterdam": 2,
        "Hamburg": 4,
        "Salzburg": 4,
    }
    total_days = 25

    # Build direct flight graph (directed for the specified one, undirected for the rest)
    undirected_edges = [
        ("Paris", "Venice"),
        ("Barcelona", "Amsterdam"),
        ("Amsterdam", "Warsaw"),
        ("Amsterdam", "Vilnius"),
        ("Barcelona", "Warsaw"),
        ("Warsaw", "Venice"),
        ("Amsterdam", "Hamburg"),
        ("Barcelona", "Hamburg"),
        ("Barcelona", "Florence"),
        ("Barcelona", "Venice"),
        ("Paris", "Hamburg"),
        ("Paris", "Vilnius"),
        ("Paris", "Amsterdam"),
        ("Paris", "Florence"),
        ("Florence", "Amsterdam"),
        ("Vilnius", "Warsaw"),
        ("Barcelona", "Tallinn"),
        ("Paris", "Warsaw"),
        ("Tallinn", "Warsaw"),
        ("Amsterdam", "Tallinn"),
        ("Paris", "Tallinn"),
        ("Paris", "Barcelona"),
        ("Venice", "Hamburg"),
        ("Warsaw", "Hamburg"),
        ("Hamburg", "Salzburg"),
        ("Amsterdam", "Venice"),
    ]
    directed_edges = [
        ("Tallinn", "Vilnius"),
    ]

    direct = set()
    for a, b in undirected_edges:
        direct.add((a, b))
        direct.add((b, a))
    for a, b in directed_edges:
        direct.add((a, b))

    def has_direct(a, b):
        return (a, b) in direct

    # Positions P1..P10 represent the ordered chain of cities
    problem = Problem()
    pos_vars = [f"P{i}" for i in range(1, 11)]

    # Fix key anchored positions by windows
    fixed = {
        "P1": ["Paris"],       # Paris must be days 1-2
        "P2": ["Barcelona"],   # Barcelona must be days 2-6
        "P9": ["Hamburg"],     # Hamburg must be days 19-22
        "P10": ["Salzburg"],   # Salzburg must be days 22-25
    }

    remaining_cities = [c for c in cities if c not in ["Paris", "Barcelona", "Hamburg", "Salzburg"]]

    for pv in pos_vars:
        if pv in fixed:
            problem.addVariable(pv, fixed[pv])
        else:
            problem.addVariable(pv, remaining_cities)

    # All positions must be different cities
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Custom constraint to enforce flights and all time-window constraints
    def itinerary_constraint(*assignment):
        order = list(assignment)
        if None in order:
            # If partial assignment occurs, defer decision (python-constraint may not call with partials,
            # but return True to avoid premature rejection).
            return True

        # Compute start days based on chain with 1-day overlap between consecutive cities
        starts = {}
        ends = {}
        s = 1
        for city in order:
            starts[city] = s
            ends[city] = s + durations[city] - 1
            s = ends[city]  # next start equals previous end to count overlap as being in both cities

        # Check the chain covers exactly 25 days from Day 1 to Day 25
        if starts[order[0]] != 1:
            return False
        if ends[order[-1]] != total_days:
            return False

        # Enforce direct flights between consecutive cities (direction matters for directed edge)
        for i in range(len(order) - 1):
            if not has_direct(order[i], order[i + 1]):
                return False

        # Time window constraints:
        # Paris workshop Day 1-2, and Paris duration is 2 -> must be exactly Day 1-2
        if not (starts["Paris"] == 1 and ends["Paris"] == 2):
            return False

        # Barcelona 5 days, meet friends Day 2-6 -> exactly Day 2-6
        if not (starts["Barcelona"] == 2 and ends["Barcelona"] == 6):
            return False

        # Hamburg 4 days, conference Day 19-22 -> exactly Day 19-22
        if not (starts["Hamburg"] == 19 and ends["Hamburg"] == 22):
            return False

        # Salzburg 4 days, wedding Day 22-25 -> exactly Day 22-25
        if not (starts["Salzburg"] == 22 and ends["Salzburg"] == 25):
            return False

        # Tallinn 2 days, meet friend Day 11-12 -> exactly Day 11-12
        if not (starts["Tallinn"] == 11 and ends["Tallinn"] == 12):
            return False

        # All duration checks are implicitly enforced by construction.
        return True

    problem.addConstraint(itinerary_constraint, pos_vars)

    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    # Build ordered list
    ordered_cities = [solution[f"P{i}"] for i in range(1, 11)]

    # Compute start/end days for output
    itinerary = []
    s = 1
    for city in ordered_cities:
        e = s + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })
        s = e  # overlap day counts in both

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
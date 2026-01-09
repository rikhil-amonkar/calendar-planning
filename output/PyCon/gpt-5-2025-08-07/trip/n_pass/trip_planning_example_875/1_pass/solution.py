import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Trip parameters
    total_days = 20
    cities = ["Venice", "Edinburgh", "Krakow", "Stuttgart", "Split", "Athens", "Mykonos"]

    # Required durations in each city
    durations = {
        "Stuttgart": 3,
        "Edinburgh": 4,
        "Athens": 4,
        "Split": 2,
        "Krakow": 4,
        "Venice": 5,
        "Mykonos": 4,
    }

    # Direct flight connections (undirected)
    direct_flights = {
        ("Krakow", "Split"),
        ("Split", "Athens"),
        ("Edinburgh", "Krakow"),
        ("Venice", "Stuttgart"),
        ("Krakow", "Stuttgart"),
        ("Edinburgh", "Stuttgart"),
        ("Stuttgart", "Athens"),
        ("Venice", "Edinburgh"),
        ("Athens", "Mykonos"),
        ("Venice", "Athens"),
        ("Stuttgart", "Split"),
        ("Edinburgh", "Athens"),
    }
    allowed_edges = {frozenset(edge) for edge in direct_flights}

    # Fixed window requirements mapped to start days (inclusive windows match durations)
    # - Krakow 4 days includes days 8-11 -> start 8
    # - Stuttgart 3 days includes days 11-13 -> start 11
    # - Split 2 days includes days 13-14 -> start 13
    fixed_starts = {
        "Krakow": 8,
        "Stuttgart": 11,
        "Split": 13,
    }

    # Build CSP
    problem = Problem()

    # Order variables: positions 1..7 each holds a city
    order_vars = [f"Order{i}" for i in range(1, 8)]
    for var in order_vars:
        problem.addVariable(var, cities)
    problem.addConstraint(AllDifferentConstraint(), order_vars)

    # Start day variables for each city
    start_vars = {city: f"Start_{city}" for city in cities}
    for city in cities:
        if city in fixed_starts:
            problem.addVariable(start_vars[city], [fixed_starts[city]])
        else:
            problem.addVariable(start_vars[city], list(range(1, total_days + 1)))

    # Constraint: adjacency must have a direct flight
    def adjacency_constraint(o1, o2, o3, o4, o5, o6, o7):
        order = [o1, o2, o3, o4, o5, o6, o7]
        for i in range(6):
            if frozenset({order[i], order[i + 1]}) not in allowed_edges:
                return False
        return True

    problem.addConstraint(adjacency_constraint, order_vars)

    # Constraint: chain of contiguous stays with overlap on travel days
    # s_{k+1} = s_k + d_k - 1
    # Start of first city = 1, end of last city = total_days
    def chain_constraint(o1, o2, o3, o4, o5, o6, o7,
                         s_Venice, s_Edinburgh, s_Krakow, s_Stuttgart, s_Split, s_Athens, s_Mykonos):
        order = [o1, o2, o3, o4, o5, o6, o7]
        start_map = {
            "Venice": s_Venice,
            "Edinburgh": s_Edinburgh,
            "Krakow": s_Krakow,
            "Stuttgart": s_Stuttgart,
            "Split": s_Split,
            "Athens": s_Athens,
            "Mykonos": s_Mykonos,
        }

        # First city must start on Day 1
        if start_map[order[0]] != 1:
            return False

        # Chain continuity with overlap on travel days
        for i in range(6):
            A = order[i]
            B = order[i + 1]
            if start_map[B] != start_map[A] + durations[A] - 1:
                return False

        # Last city's end day must be total_days
        last_city = order[-1]
        if start_map[last_city] + durations[last_city] - 1 != total_days:
            return False

        return True

    problem.addConstraint(
        chain_constraint,
        order_vars + [start_vars[c] for c in cities]
    )

    # Solve
    solution = problem.getSolution()
    if not solution:
        # Fallback: output empty itinerary if no solution found (should not happen here)
        print(json.dumps({"itinerary": []}))
        return

    # Build itinerary from solution
    itinerary_entries = []
    for city in cities:
        s = solution[start_vars[city]]
        e = s + durations[city] - 1
        itinerary_entries.append((s, e, city))

    # Sort by start day
    itinerary_entries.sort(key=lambda x: x[0])

    itinerary = []
    for s, e, city in itinerary_entries:
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Cities and required stay durations (in days)
    durations = {
        "Santorini": 3,
        "Valencia": 4,
        "Madrid": 2,
        "Seville": 2,
        "Bucharest": 3,
        "Vienna": 4,
        "Riga": 4,
        "Tallinn": 5,
        "Krakow": 5,
        "Frankfurt": 4,
    }

    cities = list(durations.keys())

    # Build directed flight graph from provided connections
    edges = set()

    def add_undirected(a, b):
        edges.add((a, b))
        edges.add((b, a))

    def add_directed(a, b):
        edges.add((a, b))

    # Given connections:
    add_undirected("Vienna", "Bucharest")
    add_undirected("Santorini", "Madrid")
    add_undirected("Seville", "Valencia")
    add_undirected("Vienna", "Seville")
    add_undirected("Madrid", "Valencia")
    add_undirected("Bucharest", "Riga")
    add_undirected("Valencia", "Bucharest")
    add_undirected("Santorini", "Bucharest")
    add_undirected("Vienna", "Valencia")
    add_undirected("Vienna", "Madrid")
    add_undirected("Valencia", "Krakow")
    add_undirected("Valencia", "Frankfurt")
    add_undirected("Krakow", "Frankfurt")
    add_directed("Riga", "Tallinn")
    add_undirected("Vienna", "Krakow")
    add_undirected("Vienna", "Frankfurt")
    add_undirected("Madrid", "Seville")
    add_undirected("Santorini", "Vienna")
    add_undirected("Vienna", "Riga")
    add_undirected("Frankfurt", "Tallinn")
    add_undirected("Frankfurt", "Bucharest")
    add_undirected("Madrid", "Bucharest")
    add_undirected("Frankfurt", "Riga")
    add_undirected("Madrid", "Frankfurt")

    # Fixed start days for specific cities based on event windows
    required_starts = {
        "Vienna": 3,    # Wedding days 3-6 (4 days)
        "Madrid": 6,    # Show days 6-7 (2 days)
        "Krakow": 11,   # Friends days 11-15 (5 days)
        "Riga": 20,     # Conference days 20-23 (4 days)
        "Tallinn": 23,  # Workshop days 23-27 (5 days)
    }

    # Setup CSP
    problem = Problem()
    pos_vars = [f"pos{i}" for i in range(1, 11)]
    for v in pos_vars:
        problem.addVariable(v, cities)

    # All cities exactly once
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Adjacency must be a direct flight (directed)
    for i in range(10 - 1):
        def adjacency_ok(a, b, edges=edges):
            return (a, b) in edges
        problem.addConstraint(adjacency_ok, (pos_vars[i], pos_vars[i + 1]))

    # Global constraint to enforce the day schedule with overlaps and fixed events
    def schedule_constraint(*assigned):
        # assigned is in order pos1..pos10 -> list of cities
        order = list(assigned)
        # Compute start days S for each position (1-based day count)
        S = [1]  # S[0] for pos1
        for i in range(9):  # up to pos10 start
            prev_city = order[i]
            S.append(S[-1] + durations[prev_city] - 1)

        # Ensure the entire trip fits exactly into 27 days
        last_city = order[-1]
        end_last = S[-1] + durations[last_city] - 1
        if end_last != 27:
            return False

        # Enforce fixed start days for specified cities
        for city, start_day in required_starts.items():
            try:
                idx = order.index(city)  # 0-based index of the city in order
            except ValueError:
                return False
            if S[idx] != start_day:
                return False

        return True

    problem.addConstraint(schedule_constraint, pos_vars)

    # Solve
    solutions = problem.getSolutions()

    if not solutions:
        print(json.dumps({"itinerary": []}))
        return

    # Choose the first solution (deterministic enough for our constraints)
    sol = solutions[0]

    # Build the itinerary with day ranges
    order = [sol[v] for v in pos_vars]
    # Compute start days
    S = [1]
    for i in range(9):
        prev_city = order[i]
        S.append(S[-1] + durations[prev_city] - 1)

    itinerary = []
    for i, city in enumerate(order):
        start = S[i]
        end = start + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
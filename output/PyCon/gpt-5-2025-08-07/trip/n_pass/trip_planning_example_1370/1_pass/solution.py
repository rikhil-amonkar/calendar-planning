import json
from constraint import Problem, AllDifferentConstraint

def build_adjacency():
    # Directed adjacency for flights
    adj = set()

    def add_undirected(a, b):
        adj.add((a, b))
        adj.add((b, a))

    def add_directed(a, b):
        adj.add((a, b))

    # Flights list as per problem statement
    add_undirected("Paris", "Krakow")
    add_undirected("Paris", "Amsterdam")
    add_undirected("Paris", "Split")
    add_directed("Vilnius", "Munich")
    add_undirected("Paris", "Geneva")
    add_undirected("Amsterdam", "Geneva")
    add_undirected("Munich", "Split")
    add_undirected("Split", "Krakow")
    add_undirected("Munich", "Amsterdam")
    add_undirected("Budapest", "Amsterdam")
    add_undirected("Split", "Geneva")
    add_undirected("Vilnius", "Split")
    add_undirected("Munich", "Geneva")
    add_undirected("Munich", "Krakow")
    add_directed("Krakow", "Vilnius")
    add_undirected("Vilnius", "Amsterdam")
    add_undirected("Budapest", "Paris")
    add_undirected("Krakow", "Amsterdam")
    add_undirected("Vilnius", "Paris")
    add_undirected("Budapest", "Geneva")
    add_undirected("Split", "Amsterdam")
    add_undirected("Santorini", "Geneva")
    add_undirected("Amsterdam", "Santorini")
    add_undirected("Munich", "Budapest")
    add_undirected("Munich", "Paris")
    return adj

def compute_itinerary():
    # Cities and durations
    cities = [
        "Santorini",
        "Krakow",
        "Paris",
        "Vilnius",
        "Munich",
        "Geneva",
        "Amsterdam",
        "Budapest",
        "Split",
    ]

    durations = {
        "Santorini": 5,
        "Krakow": 5,
        "Paris": 5,
        "Vilnius": 3,
        "Munich": 5,
        "Geneva": 2,
        "Amsterdam": 4,
        "Budapest": 5,
        "Split": 4,
    }

    # Time window constraints: city must overlap these ranges (inclusive)
    windows = {
        "Paris": (11, 15),
        "Krakow": (18, 22),
        "Santorini": (25, 29),
    }

    adjacency = build_adjacency()

    problem = Problem()

    # Position variable for each city: 0..8 in the sequence
    for c in cities:
        problem.addVariable(c, range(len(cities)))

    # All cities occupy unique positions
    problem.addConstraint(AllDifferentConstraint(), cities)

    # Optional ordering hint to speed up search (consistent with windows)
    def precedence(p, k, s):
        return p < k and k < s
    problem.addConstraint(precedence, ("Paris", "Krakow", "Santorini"))

    # Core schedule constraint: enforce direct flights, 30-day chain with 1-day overlaps,
    # and window intersections
    def schedule_constraint(*pos_values, cities=cities, durations=durations, windows=windows, adjacency=adjacency):
        pos = dict(zip(cities, pos_values))

        # Build ordered list by position
        order = sorted(cities, key=lambda c: pos[c])

        # Check consecutive direct flights
        for i in range(len(order) - 1):
            a, b = order[i], order[i + 1]
            if (a, b) not in adjacency:
                return False

        # Compute start/end with 1-day overlaps
        starts = {}
        ends = {}
        starts[order[0]] = 1
        ends[order[0]] = starts[order[0]] + durations[order[0]] - 1
        for i in range(1, len(order)):
            prev, cur = order[i - 1], order[i]
            starts[cur] = ends[prev]  # overlap exactly on travel day
            ends[cur] = starts[cur] + durations[cur] - 1

        # Window intersections
        def intersects(a_start, a_end, w_start, w_end):
            return not (a_end < w_start or a_start > w_end)

        for city, (w_start, w_end) in windows.items():
            if not intersects(starts[city], ends[city], w_start, w_end):
                return False

        # Ensure the overall schedule spans exactly to day 30 (always true if sums match,
        # but we check for safety)
        if ends[order[-1]] != 30:
            return False

        # All starts must be >= 1 and <= 30
        for c in cities:
            if starts[c] < 1 or ends[c] > 30:
                return False

        return True

    problem.addConstraint(schedule_constraint, cities)

    solution = problem.getSolution()
    if not solution:
        raise RuntimeError("No feasible itinerary found with given constraints.")

    # Build the itinerary output
    order = sorted(cities, key=lambda c: solution[c])

    # Recompute starts/ends for the solution
    starts = {}
    ends = {}
    starts[order[0]] = 1
    ends[order[0]] = starts[order[0]] + durations[order[0]] - 1
    for i in range(1, len(order)):
        prev, cur = order[i - 1], order[i]
        starts[cur] = ends[prev]
        ends[cur] = starts[cur] + durations[cur] - 1

    itinerary = []
    for c in order:
        itinerary.append({
            "day_range": f"Day {starts[c]}-{ends[c]}",
            "place": c
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))
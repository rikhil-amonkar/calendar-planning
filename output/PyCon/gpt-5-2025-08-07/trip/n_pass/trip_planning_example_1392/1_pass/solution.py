import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and durations (in days)
    cities = [
        "Venice", "Nice", "Naples", "Valencia", "Stuttgart",
        "Split", "Amsterdam", "Barcelona", "Porto"
    ]
    durations = {
        "Venice": 5,
        "Nice": 2,
        "Naples": 3,
        "Valencia": 5,
        "Stuttgart": 2,
        "Split": 5,
        "Amsterdam": 4,
        "Barcelona": 2,
        "Porto": 4
    }

    # Total trip length (unique days)
    TOTAL_DAYS = 24

    # Direct flight pairs (undirected)
    direct_pairs = [
        ("Venice", "Nice"),
        ("Naples", "Amsterdam"),
        ("Barcelona", "Nice"),
        ("Amsterdam", "Nice"),
        ("Stuttgart", "Valencia"),
        ("Stuttgart", "Porto"),
        ("Split", "Stuttgart"),
        ("Split", "Naples"),
        ("Valencia", "Amsterdam"),
        ("Barcelona", "Porto"),
        ("Valencia", "Naples"),
        ("Venice", "Amsterdam"),
        ("Barcelona", "Naples"),
        ("Barcelona", "Valencia"),
        ("Split", "Amsterdam"),
        ("Barcelona", "Venice"),
        ("Stuttgart", "Amsterdam"),
        ("Naples", "Nice"),
        ("Venice", "Stuttgart"),
        ("Split", "Barcelona"),
        ("Porto", "Nice"),
        ("Barcelona", "Stuttgart"),
        ("Venice", "Naples"),
        ("Porto", "Amsterdam"),
        ("Porto", "Valencia"),
        ("Stuttgart", "Naples"),
        ("Barcelona", "Amsterdam"),
    ]
    edges = set(frozenset(p) for p in direct_pairs)

    # Variables: sequence positions 1..9 each holding a city
    vars_order = [f"pos{i}" for i in range(1, 10)]

    problem = Problem()
    for v in vars_order:
        problem.addVariable(v, cities)
    problem.addConstraint(AllDifferentConstraint(), vars_order)

    # Custom feasibility constraint enforcing:
    # - Direct flights between consecutive cities
    # - Overlap-day travel rule (start(next) = end(current))
    # - Total unique days = 24 (end of last = 24, start of first = 1)
    # - Fixed-day constraints:
    #   * Barcelona on days 5-6 (start=5)
    #   * Venice on days 6-10 (start=6) and immediately after Barcelona
    #   * Nice on days 23-24 (start=23)
    #   * Naples intersects any of days 18-20 (inclusive)
    def feasibility(*order):
        order = list(order)
        # Adjacency check (direct flights)
        for i in range(8):
            if frozenset((order[i], order[i+1])) not in edges:
                return False

        # Compute starts and ends using durations and overlap rule
        starts = [0] * 9
        ends = [0] * 9
        starts[0] = 1
        ends[0] = starts[0] + durations[order[0]] - 1
        for i in range(1, 9):
            starts[i] = ends[i - 1]
            ends[i] = starts[i] + durations[order[i]] - 1

        # Ensure total unique days is exactly TOTAL_DAYS
        if ends[-1] != TOTAL_DAYS:
            return False

        # Barcelona on days 5-6
        try:
            idx_barcelona = order.index("Barcelona")
        except ValueError:
            return False
        if starts[idx_barcelona] != 5:
            return False

        # Venice on days 6-10 and directly after Barcelona
        try:
            idx_venice = order.index("Venice")
        except ValueError:
            return False
        if starts[idx_venice] != 6:
            return False
        if idx_venice != idx_barcelona + 1:
            return False

        # Nice on days 23-24
        try:
            idx_nice = order.index("Nice")
        except ValueError:
            return False
        if starts[idx_nice] != 23:
            return False

        # Naples intersects day 18..20 (inclusive)
        try:
            idx_naples = order.index("Naples")
        except ValueError:
            return False
        if not (starts[idx_naples] <= 20 and ends[idx_naples] >= 18):
            return False

        return True

    problem.addConstraint(feasibility, vars_order)

    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"itinerary": []}))
        return

    # Build the ordered list and compute the final day ranges
    order = [solution[v] for v in vars_order]
    starts = [0] * 9
    ends = [0] * 9
    starts[0] = 1
    ends[0] = starts[0] + durations[order[0]] - 1
    for i in range(1, 9):
        starts[i] = ends[i - 1]
        ends[i] = starts[i] + durations[order[i]] - 1

    itinerary = []
    for i in range(9):
        itinerary.append({
            "day_range": f"Day {starts[i]}-{ends[i]}",
            "place": order[i]
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
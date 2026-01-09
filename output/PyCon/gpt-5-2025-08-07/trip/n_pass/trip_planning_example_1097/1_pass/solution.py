import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Cities and required stay durations (in days)
    cities = [
        "Reykjavik", "Riga", "Oslo", "Lyon",
        "Dubrovnik", "Madrid", "Warsaw", "London"
    ]
    durations = {
        "Reykjavik": 4,
        "Riga": 2,
        "Oslo": 3,
        "Lyon": 5,
        "Dubrovnik": 2,
        "Madrid": 2,
        "Warsaw": 4,
        "London": 3
    }

    # Directed flight edges; "A and B" -> both directions; "from A to B" -> A->B only
    edges = set()
    def add_undirected(a, b):
        edges.add((a, b))
        edges.add((b, a))
    def add_directed(a, b):
        edges.add((a, b))

    add_undirected("Warsaw", "Reykjavik")
    add_undirected("Oslo", "Madrid")
    add_undirected("Warsaw", "Riga")
    add_undirected("Lyon", "London")
    add_undirected("Madrid", "London")
    add_undirected("Warsaw", "London")
    add_directed("Reykjavik", "Madrid")
    add_undirected("Warsaw", "Oslo")
    add_undirected("Oslo", "Dubrovnik")
    add_undirected("Oslo", "Reykjavik")
    add_undirected("Riga", "Oslo")
    add_undirected("Oslo", "Lyon")
    add_undirected("Oslo", "London")
    add_undirected("London", "Reykjavik")
    add_undirected("Warsaw", "Madrid")
    add_undirected("Madrid", "Lyon")
    add_undirected("Dubrovnik", "Madrid")

    total_days = 18
    num_cities = len(cities)
    # With 8 cities, 7 transitions -> 7 overlap days; sum(durations)=25 => 25-7=18 calendar days
    assert sum(durations.values()) - (num_cities - 1) == total_days

    # Build solver
    problem = Problem()
    position_vars = [f"C{i}" for i in range(1, num_cities + 1)]
    for var in position_vars:
        problem.addVariable(var, cities)
    problem.addConstraint(AllDifferentConstraint(), position_vars)

    # Main constraint including:
    # - flight adjacency (directed where applicable)
    # - calendar alignment with overlap (flight day counted in both cities)
    # - event windows: Riga intersect {4,5}, Dubrovnik intersect {7,8}
    # - total calendar end day must be 18
    def itinerary_constraint(*order):
        order = list(order)  # [C1..C8]
        # Check adjacency
        for i in range(len(order) - 1):
            if (order[i], order[i + 1]) not in edges:
                return False

        # Compute start days with overlap = 1 day between consecutive cities
        starts = [0] * num_cities
        starts[0] = 1
        for i in range(1, num_cities):
            prev_city = order[i - 1]
            starts[i] = starts[i - 1] + durations[prev_city] - 1

        # Verify the end day equals total_days
        last_city = order[-1]
        end_day = starts[-1] + durations[last_city] - 1
        if end_day != total_days:
            return False

        # Build occupancy windows per city
        occ = {}
        for idx, city in enumerate(order):
            s = starts[idx]
            e = s + durations[city] - 1
            occ[city] = (s, e)

        # Friend meet in Riga between day 4 and day 5 -> be in Riga on day 4 or 5
        if "Riga" not in occ:
            return False
        r_s, r_e = occ["Riga"]
        if not ((r_s <= 4 <= r_e) or (r_s <= 5 <= r_e)):
            return False

        # Wedding in Dubrovnik between day 7 and 8 -> be in Dubrovnik on day 7 or 8
        if "Dubrovnik" not in occ:
            return False
        d_s, d_e = occ["Dubrovnik"]
        if not ((d_s <= 7 <= d_e) or (d_s <= 8 <= d_e)):
            return False

        return True

    problem.addConstraint(itinerary_constraint, position_vars)

    solution = problem.getSolution()
    if not solution:
        # No valid itinerary found; return empty
        print(json.dumps({"itinerary": []}, ensure_ascii=False))
        return

    # Reconstruct the ordered itinerary and day ranges
    ordered_cities = [solution[var] for var in position_vars]
    starts = [0] * num_cities
    starts[0] = 1
    for i in range(1, num_cities):
        prev_city = ordered_cities[i - 1]
        starts[i] = starts[i - 1] + durations[prev_city] - 1
    itinerary = []
    for i, city in enumerate(ordered_cities):
        s = starts[i]
        e = s + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
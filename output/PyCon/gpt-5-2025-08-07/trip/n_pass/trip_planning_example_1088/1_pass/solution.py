import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Cities and required stay durations (in days)
    cities = ["Oslo", "Stuttgart", "Reykjavik", "Split", "Geneva", "Porto", "Tallinn", "Stockholm"]
    durations = {
        "Oslo": 5,
        "Stuttgart": 5,
        "Reykjavik": 2,
        "Split": 3,
        "Geneva": 2,
        "Porto": 3,
        "Tallinn": 5,
        "Stockholm": 3
    }
    total_days = 21

    # Build undirected direct-flight graph from provided pairs
    edges = set()
    def add_edge(a, b):
        edges.add(frozenset((a, b)))

    # From the provided list of direct flights (interpreted as undirected)
    add_edge("Reykjavik", "Stuttgart")
    add_edge("Reykjavik", "Stockholm")
    add_edge("Reykjavik", "Tallinn")
    add_edge("Stockholm", "Oslo")
    add_edge("Stuttgart", "Porto")
    add_edge("Oslo", "Split")
    add_edge("Stockholm", "Stuttgart")
    add_edge("Reykjavik", "Oslo")
    add_edge("Oslo", "Geneva")
    add_edge("Stockholm", "Split")
    add_edge("Split", "Stuttgart")
    add_edge("Tallinn", "Oslo")
    add_edge("Stockholm", "Geneva")
    add_edge("Oslo", "Porto")
    add_edge("Geneva", "Porto")
    add_edge("Geneva", "Split")
    # Disambiguated pair present in the textual list segment ("Stockholm and Tallinn")
    add_edge("Stockholm", "Tallinn")

    # CSP: position of each city in the sequence 1..8
    problem = Problem()
    for c in cities:
        problem.addVariable(c, range(1, len(cities) + 1))
    problem.addConstraint(AllDifferentConstraint(), cities)

    # Reykjavik must be first (days 1-2), Porto last (days 19-21)
    problem.addConstraint(lambda p: p == 1, ("Reykjavik",))
    problem.addConstraint(lambda p: p == 8, ("Porto",))

    # Single global constraint to enforce:
    # - Direct flights between consecutive cities
    # - Correct day ranges and fixed events (RKV conf days 1-2; Porto days 19-21)
    # - Stockholm meet friend between day 2 and day 4 (at least one day overlap)
    def global_constraint(*pos_vals):
        pos = dict(zip(cities, pos_vals))
        # Order cities by position
        order = sorted(cities, key=lambda x: pos[x])

        # Check direct flights between consecutive cities (undirected)
        for i in range(len(order) - 1):
            if frozenset((order[i], order[i + 1])) not in edges:
                return False

        # Compute contiguous block start/end with shared flight days
        start_day = 1
        start_map = {}
        end_map = {}
        for city in order:
            start_map[city] = start_day
            end_map[city] = start_day + durations[city] - 1
            start_day = end_map[city]  # Next city starts on flight day (shared)

        # Ensure last day equals total_days
        if end_map[order[-1]] != total_days:
            return False

        # Fixed events/constraints
        # Reykjavik: Day 1-2 conference
        if start_map["Reykjavik"] != 1 or end_map["Reykjavik"] != 2:
            return False

        # Porto: workshop days 19-21
        if start_map["Porto"] != 19 or end_map["Porto"] != 21:
            return False

        # Stockholm: meet friend between day 2 and day 4 (inclusive overlap)
        if not (start_map["Stockholm"] <= 4 and end_map["Stockholm"] >= 2):
            return False

        return True

    problem.addConstraint(global_constraint, cities)

    solution = problem.getSolution()

    output = {"itinerary": []}
    if solution:
        # Build itinerary blocks
        order = sorted(cities, key=lambda x: solution[x])
        # Compute day ranges
        start_day = 1
        for city in order:
            s = start_day
            e = s + durations[city] - 1
            output["itinerary"].append({
                "day_range": f"Day {s}-{e}",
                "place": city
            })
            start_day = e  # shared flight day
    else:
        # No solution found, output empty itinerary
        output["itinerary"] = []

    print(json.dumps(output))

if __name__ == "__main__":
    main()
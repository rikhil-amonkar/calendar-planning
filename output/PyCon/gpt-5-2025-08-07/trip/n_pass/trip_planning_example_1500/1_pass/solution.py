import json
from constraint import Problem, AllDifferentConstraint

def build_edges():
    edges = set()

    def add_undirected(a, b):
        edges.add((a, b))
        edges.add((b, a))

    def add_directed(a, b):
        edges.add((a, b))

    # Undirected edges ("X and Y")
    add_undirected("London", "Hamburg")
    add_undirected("London", "Reykjavik")
    add_undirected("Milan", "Barcelona")
    add_undirected("Reykjavik", "Barcelona")
    add_undirected("Stockholm", "Reykjavik")
    add_undirected("London", "Stuttgart")
    add_undirected("Milan", "Zurich")
    add_undirected("London", "Barcelona")
    add_undirected("Stockholm", "Hamburg")
    add_undirected("Zurich", "Barcelona")
    add_undirected("Stockholm", "Stuttgart")
    add_undirected("Milan", "Hamburg")
    add_undirected("Stockholm", "Tallinn")
    add_undirected("Hamburg", "Bucharest")
    add_undirected("London", "Bucharest")
    add_undirected("Milan", "Stockholm")
    add_undirected("Stuttgart", "Hamburg")
    add_undirected("London", "Zurich")
    add_undirected("Milan", "Stuttgart")
    add_undirected("Stockholm", "Barcelona")
    add_undirected("London", "Milan")
    add_undirected("Zurich", "Hamburg")
    add_undirected("Bucharest", "Barcelona")
    add_undirected("Zurich", "Stockholm")
    add_undirected("Barcelona", "Tallinn")
    add_undirected("Zurich", "Tallinn")
    add_undirected("Hamburg", "Barcelona")
    add_undirected("Stuttgart", "Barcelona")
    add_undirected("Zurich", "Reykjavik")
    add_undirected("Zurich", "Bucharest")

    # Directed edge ("from X to Y")
    add_directed("Reykjavik", "Stuttgart")

    return edges

def main():
    cities = [
        "London",
        "Milan",
        "Zurich",
        "Stockholm",
        "Reykjavik",
        "Stuttgart",
        "Hamburg",
        "Bucharest",
        "Barcelona",
        "Tallinn",
    ]

    durations = {
        "London": 3,      # Days 1-3 (Annual show)
        "Milan": 5,       # Meet friends between day 3 and day 7
        "Zurich": 2,      # Conference days 7-8
        "Stockholm": 2,
        "Reykjavik": 5,   # Visit relatives days 9-13
        "Stuttgart": 5,
        "Hamburg": 5,
        "Bucharest": 2,
        "Barcelona": 4,
        "Tallinn": 4,
    }

    edges = build_edges()

    problem = Problem()
    pos_vars = [f"p{i}" for i in range(1, 11)]
    for v in pos_vars:
        problem.addVariable(v, cities)

    # All cities must be visited exactly once
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Direct flight adjacency constraints between consecutive positions
    for i in range(1, 10):
        a = f"p{i}"
        b = f"p{i+1}"
        problem.addConstraint(lambda x, y, E=edges: (x, y) in E, (a, b))

    # Anchor key time-window constraints via fixed positions implied by day math:
    # Position day starts are determined by durations and 1-day overlaps:
    # p1 start = 1
    # p2 start = 3 (since p1 is 3 days and next starts at previous end)
    # p3 start = 7 (3 + 5 - 1)
    # p4 start = 8 (7 + 2 - 1)
    # p5 start = 9 (8 + 2 - 1)
    # Enforce cities at these positions to satisfy hard requirements.

    # Days 1-3 in London (annual show)
    problem.addConstraint(lambda c: c == "London", ("p1",))

    # Meet friends in Milan between day 3 and day 7 -> Milan spans exactly days 3-7
    problem.addConstraint(lambda c: c == "Milan", ("p2",))

    # Zurich conference days 7-8
    problem.addConstraint(lambda c: c == "Zurich", ("p3",))

    # Reykjavik relatives days 9-13
    problem.addConstraint(lambda c: c == "Reykjavik", ("p5",))

    # Solve
    solution = problem.getSolution()

    if not solution:
        print(json.dumps({"itinerary": []}))
        return

    # Build itinerary with computed day ranges
    ordered_cities = [solution[f"p{i}"] for i in range(1, 11)]

    itinerary = []
    current_start = 1
    for city in ordered_cities:
        length = durations[city]
        start = current_start
        end = start + length - 1
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
        # Next segment starts at previous end (flight day counts for both)
        current_start = end

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
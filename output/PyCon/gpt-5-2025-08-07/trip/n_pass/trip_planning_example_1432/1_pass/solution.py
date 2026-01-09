import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Cities and durations (in days)
    cities = [
        "Frankfurt", "Salzburg", "Athens", "Reykjavik", "Bucharest",
        "Valencia", "Vienna", "Amsterdam", "Stockholm", "Riga"
    ]
    durations = {
        "Frankfurt": 4,
        "Salzburg": 5,
        "Athens": 5,
        "Reykjavik": 5,
        "Bucharest": 3,
        "Valencia": 2,
        "Vienna": 5,
        "Amsterdam": 3,
        "Stockholm": 3,
        "Riga": 3,
    }

    # Build directed flight edges
    edges = set()
    def add_undirected(a, b):
        edges.add((a, b))
        edges.add((b, a))
    def add_direct(a, b):
        edges.add((a, b))

    # Given direct flights
    add_undirected("Valencia", "Frankfurt")
    add_undirected("Vienna", "Bucharest")
    add_direct("Valencia", "Athens")
    add_undirected("Athens", "Bucharest")
    add_undirected("Riga", "Frankfurt")
    add_undirected("Stockholm", "Athens")
    add_undirected("Amsterdam", "Bucharest")
    add_direct("Athens", "Riga")
    add_undirected("Amsterdam", "Frankfurt")
    add_undirected("Stockholm", "Vienna")
    add_undirected("Vienna", "Riga")
    add_undirected("Amsterdam", "Reykjavik")
    add_undirected("Reykjavik", "Frankfurt")
    add_undirected("Stockholm", "Amsterdam")
    add_undirected("Amsterdam", "Valencia")
    add_undirected("Vienna", "Frankfurt")
    add_undirected("Valencia", "Bucharest")
    add_undirected("Bucharest", "Frankfurt")
    add_undirected("Stockholm", "Frankfurt")
    add_undirected("Valencia", "Vienna")
    add_direct("Reykjavik", "Athens")
    add_undirected("Frankfurt", "Salzburg")
    add_undirected("Amsterdam", "Vienna")
    add_undirected("Stockholm", "Reykjavik")
    add_undirected("Amsterdam", "Riga")
    add_undirected("Stockholm", "Riga")
    add_undirected("Vienna", "Reykjavik")
    add_undirected("Amsterdam", "Athens")
    add_undirected("Athens", "Frankfurt")
    add_undirected("Vienna", "Athens")
    add_undirected("Riga", "Bucharest")

    # Total trip days
    total_days = 29

    # Set up CSP
    problem = Problem()
    var_names = [f"pos{i}" for i in range(1, 11)]
    for vn in var_names:
        problem.addVariable(vn, cities)

    # All cities must be used exactly once (permutation)
    problem.addConstraint(AllDifferentConstraint(), var_names)

    # Adjacency must be a direct flight (respect direction where specified)
    for i in range(1, 10):
        a = f"pos{i}"
        b = f"pos{i+1}"
        def flight_ok(ci, cj, edges=edges):
            if ci is None or cj is None:
                return True
            return (ci, cj) in edges
        problem.addConstraint(flight_ok, (a, b))

    # Global time and event constraints
    def time_constraints(*seq):
        # seq is tuple of 10 city names in order pos1..pos10
        seq = list(seq)
        # Compute intervals with 1-day overlap between consecutive cities
        # Start of first city is Day 1
        start_day = 1
        intervals = {}  # city -> (start, end)
        for city in seq:
            s = start_day
            e = s + durations[city] - 1
            intervals[city] = (s, e)
            start_day = e  # next city starts at current end (overlap travel day)
        trip_end = intervals[seq[-1]][1]
        # Validate overall trip duration ends on total_days
        if trip_end != total_days:
            return False

        # Helper for interval intersection
        def intersects(ci, a, b):
            s, e = intervals[ci]
            return not (e < a or s > b)

        # Hard constraints:
        # Valencia: must attend show on Day 5-6 => Valencia must be exactly Day 5-6
        if intervals["Valencia"][0] != 5 or intervals["Valencia"][1] != 6:
            return False

        # Riga conference: must be in Riga during Days 18-20 (all three days)
        if intervals["Riga"][0] != 18 or intervals["Riga"][1] != 20:
            return False

        # Athens workshop between Day 14 and Day 18 (intersection)
        if not intersects("Athens", 14, 18):
            return False

        # Vienna wedding between Day 6 and Day 10 (intersection)
        if not intersects("Vienna", 6, 10):
            return False

        # Stockholm friend meeting between Day 1 and Day 3 (intersection)
        if not intersects("Stockholm", 1, 3):
            return False

        return True

    problem.addConstraint(time_constraints, tuple(var_names))

    # Solve
    solution = problem.getSolution()
    if solution is None:
        print(json.dumps({"itinerary": []}))
        return

    # Build ordered itinerary
    ordered = [solution[f"pos{i}"] for i in range(1, 11)]
    # Compute intervals
    start_day = 1
    itinerary = []
    for city in ordered:
        s = start_day
        e = s + durations[city] - 1
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})
        start_day = e

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
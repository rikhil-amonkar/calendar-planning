import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables and constraints
    total_days = 19
    cities = ["Reykjavik", "Istanbul", "Edinburgh", "Oslo", "Stuttgart", "Bucharest"]
    durations = {
        "Reykjavik": 5,
        "Istanbul": 4,
        "Edinburgh": 5,
        "Oslo": 2,
        "Stuttgart": 3,
        "Bucharest": 5,
    }
    # Time window constraints (inclusive)
    istanbul_window = (5, 8)  # meet friends between day 5 and 8
    oslo_window = (8, 9)      # visit relatives between day 8 and 9

    # Flight graph: direct flights allowed (directed/undirected as specified)
    edges = set()

    def add_undirected(a, b):
        edges.add((a, b))
        edges.add((b, a))

    def add_directed(a, b):
        edges.add((a, b))

    add_undirected("Bucharest", "Oslo")
    add_undirected("Istanbul", "Oslo")
    add_directed("Reykjavik", "Stuttgart")
    add_undirected("Bucharest", "Istanbul")
    add_undirected("Stuttgart", "Edinburgh")
    add_undirected("Istanbul", "Edinburgh")
    add_undirected("Oslo", "Reykjavik")
    add_undirected("Istanbul", "Stuttgart")
    add_undirected("Oslo", "Edinburgh")

    # Create constraint problem
    problem = Problem()

    # Variables representing the city sequence (6 positions)
    pos_vars = [f"P{i}" for i in range(1, 7)]
    for v in pos_vars:
        problem.addVariable(v, cities)

    # All cities must be distinct (visit each once)
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Constraint function to enforce adjacency (flights), durations, overlaps, and time windows
    def itinerary_constraint(P1, P2, P3, P4, P5, P6):
        seq = [P1, P2, P3, P4, P5, P6]

        # Adjacency: only direct flights between consecutive cities
        for i in range(len(seq) - 1):
            if (seq[i], seq[i + 1]) not in edges:
                return False

        # Compute the schedule considering overlaps on transition days:
        # If flight occurs on day X, we are in both cities on day X.
        # Model: First city starts day 1, ends day = start + duration - 1
        # Next city starts on the same end day (overlap of 1 day)
        city_ranges = {}
        current_start = 1
        for city in seq:
            start = current_start
            end = start + durations[city] - 1
            city_ranges[city] = (start, end)
            current_start = end  # next city starts on the same day as previous city's end

        # End of trip must match total days
        if city_ranges[seq[-1]][1] != total_days:
            return False

        # Enforce time windows
        if city_ranges["Istanbul"] != istanbul_window:
            return False
        if city_ranges["Oslo"] != oslo_window:
            return False

        # Durations must be exact
        for c, d in durations.items():
            s, e = city_ranges[c]
            if (e - s + 1) != d:
                return False

        return True

    problem.addConstraint(
        itinerary_constraint, pos_vars
    )

    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"itinerary": []}))
        return

    # Build ordered sequence from solution
    seq = [solution[f"P{i}"] for i in range(1, 7)]

    # Compute final schedule
    schedule = []
    current_start = 1
    for city in seq:
        start = current_start
        end = start + durations[city] - 1
        schedule.append((city, start, end))
        current_start = end

    # Prepare JSON output
    itinerary = []
    for city, start, end in schedule:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
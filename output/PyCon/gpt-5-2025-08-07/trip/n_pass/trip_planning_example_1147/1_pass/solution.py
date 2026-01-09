import json
from constraint import Problem, AllDifferentConstraint

def build_adjacency():
    # Build directed adjacency from the provided direct flight list
    edges = set()
    def add_undirected(a, b):
        edges.add((a, b))
        edges.add((b, a))
    def add_directed(a, b):
        edges.add((a, b))

    # Undirected routes ("and" = both directions)
    add_undirected("Milan", "Frankfurt")
    add_undirected("Split", "Frankfurt")
    add_undirected("Milan", "Split")
    add_undirected("Brussels", "Vilnius")
    add_undirected("Brussels", "Helsinki")
    add_undirected("Istanbul", "Brussels")
    add_undirected("Milan", "Vilnius")
    add_undirected("Brussels", "Milan")
    add_undirected("Istanbul", "Helsinki")
    add_undirected("Helsinki", "Vilnius")
    add_undirected("Helsinki", "Dubrovnik")
    add_undirected("Split", "Vilnius")
    add_undirected("Istanbul", "Milan")
    add_undirected("Helsinki", "Frankfurt")
    add_undirected("Istanbul", "Vilnius")
    add_undirected("Split", "Helsinki")
    add_undirected("Milan", "Helsinki")
    add_undirected("Istanbul", "Frankfurt")
    add_undirected("Dubrovnik", "Frankfurt")
    add_undirected("Frankfurt", "Vilnius")

    # Directed routes ("from X to Y")
    add_directed("Dubrovnik", "Istanbul")
    add_directed("Brussels", "Frankfurt")

    return edges

def main():
    # Trip parameters
    cities = [
        "Brussels",
        "Helsinki",
        "Split",
        "Dubrovnik",
        "Istanbul",
        "Milan",
        "Vilnius",
        "Frankfurt",
    ]

    durations = {
        "Brussels": 3,
        "Helsinki": 3,
        "Split": 4,
        "Dubrovnik": 2,
        "Istanbul": 5,
        "Milan": 4,
        "Vilnius": 5,
        "Frankfurt": 3,
    }

    # Days and windows
    total_days = 22
    must_be_in = {
        # city: (start_day, end_day) inclusive
        "Istanbul": (1, 5),   # Show Day 1-5
        "Frankfurt": (16, 18),# Wedding Day 16-18
        "Vilnius": (18, 22),  # Workshop Day 18-22
    }

    edges = build_adjacency()

    # Constraint problem
    problem = Problem()
    positions = [f"pos{i}" for i in range(1, 9)]
    for pos in positions:
        problem.addVariable(pos, cities)

    # All cities must be used exactly once
    problem.addConstraint(AllDifferentConstraint(), tuple(positions))

    # First city must be Istanbul to cover Day 1-5
    problem.addConstraint(lambda c: c == "Istanbul", ("pos1",))

    # Flight connectivity constraints between consecutive cities (directed)
    def flight_constraint(a, b):
        return (a, b) in edges

    for i in range(1, 8):
        problem.addConstraint(flight_constraint, (f"pos{i}", f"pos{i+1}"))

    # Day alignment constraints: compute start days from order and durations with 1-day overlaps
    # S1 = 1, E1 = S1 + D1 - 1, S2 = E1, E2 = S2 + D2 - 1, etc.
    def day_alignment_constraint(*ordered_cities):
        # ordered_cities is a tuple of the cities at pos1..pos8
        # Ensure Istanbul covers Day 1-5 implicitly by being first with duration 5
        if ordered_cities[0] != "Istanbul":
            return False
        # compute starts
        starts = []
        start = 1
        for city in ordered_cities:
            starts.append(start)
            start = start + durations[city] - 1  # next start equals current end

        # Check the last city's end equals total_days
        last_start = starts[-1]
        last_end = last_start + durations[ordered_cities[-1]] - 1
        if last_end != total_days:
            return False

        # Enforce required city windows
        for city, (req_start, req_end) in must_be_in.items():
            # Find city position
            try:
                idx = ordered_cities.index(city)
            except ValueError:
                return False
            city_start = starts[idx]
            city_end = city_start + durations[city] - 1
            # City must exactly match the required window for those with specified windows
            # Because the specified days must be included and the total duration matches exactly.
            if city_start != req_start or city_end != req_end:
                return False

        return True

    problem.addConstraint(day_alignment_constraint, tuple(positions))

    # Solve
    solution = problem.getSolution()
    if not solution:
        # In the unlikely event of failure, output an empty itinerary to maintain JSON validity
        print(json.dumps({"itinerary": []}))
        return

    # Build itinerary with actual day ranges
    ordered = [solution[f"pos{i}"] for i in range(1, 9)]
    itinerary = []
    cur_start = 1
    for city in ordered:
        cur_end = cur_start + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {cur_start}-{cur_end}",
            "place": city
        })
        cur_start = cur_end  # next city starts on the same day (overlap)

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
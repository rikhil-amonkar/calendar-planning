import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and required durations (in days)
    cities = ["Brussels", "Lisbon", "Venice", "Madrid", "Santorini", "London", "Reykjavik"]
    durations = {
        "Brussels": 2,
        "Lisbon": 4,
        "Venice": 3,
        "Madrid": 5,
        "Santorini": 3,
        "London": 3,
        "Reykjavik": 3,
    }

    # Flight network: allowed directed edges (direct flights only)
    directed_edges = set()
    def add_bidirectional(a, b):
        directed_edges.add((a, b))
        directed_edges.add((b, a))
    def add_directional(a, b):
        directed_edges.add((a, b))

    add_bidirectional("Venice", "Madrid")
    add_bidirectional("Lisbon", "Reykjavik")
    add_bidirectional("Brussels", "Venice")
    add_bidirectional("Venice", "Santorini")
    add_bidirectional("Lisbon", "Venice")
    add_directional("Reykjavik", "Madrid")  # directional only
    add_bidirectional("Brussels", "London")
    add_bidirectional("Madrid", "London")
    add_bidirectional("Santorini", "London")
    add_bidirectional("London", "Reykjavik")
    add_bidirectional("Brussels", "Lisbon")
    add_bidirectional("Lisbon", "London")
    add_bidirectional("Lisbon", "Madrid")
    add_bidirectional("Madrid", "Santorini")
    add_bidirectional("Brussels", "Reykjavik")
    add_bidirectional("Brussels", "Madrid")
    add_bidirectional("Venice", "London")

    def has_direct(a, b):
        return (a, b) in directed_edges

    # Total calendar days accounting for overlaps (flying day counts for both cities)
    total_days = sum(durations.values()) - (len(cities) - 1)  # 23 - 6 = 17
    assert total_days == 17

    # Set up constraint problem over permutations (order of visiting cities)
    problem = Problem()
    pos_vars = [f"pos{i}" for i in range(1, len(cities) + 1)]
    for v in pos_vars:
        problem.addVariables([v], cities)
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Global constraint to enforce timing windows, durations, connectivity
    def itinerary_constraint(*order_tuple):
        order = list(order_tuple)

        # Compute start/end days for each city in this order
        start_day = {}
        end_day = {}
        current_start = 1
        for city in order:
            start_day[city] = current_start
            end_day[city] = current_start + durations[city] - 1
            current_start = end_day[city]  # overlap on flight day

        # Connectivity: only direct flights allowed between consecutive cities
        for i in range(len(order) - 1):
            if not has_direct(order[i], order[i + 1]):
                return False

        # Trip must span exactly Day 1 to Day 17
        if end_day[order[-1]] != total_days:
            return False

        # Brussels conference: must be in Brussels on Day 1 and Day 2
        if not (start_day["Brussels"] <= 1 <= end_day["Brussels"] and start_day["Brussels"] <= 2 <= end_day["Brussels"]):
            return False

        # Venice relatives between Day 5 and Day 7 => exactly Days 5-7 in Venice
        if not (start_day["Venice"] == 5 and end_day["Venice"] == 7):
            return False

        # Madrid wedding between Day 7 and Day 11 => exactly Days 7-11 in Madrid
        if not (start_day["Madrid"] == 7 and end_day["Madrid"] == 11):
            return False

        # Implicit duration checks are satisfied by construction, but ensure correctness
        for c in cities:
            if end_day[c] - start_day[c] + 1 != durations[c]:
                return False

        return True

    problem.addConstraint(itinerary_constraint, pos_vars)

    solutions = problem.getSolutions()
    if not solutions:
        print(json.dumps({"error": "No feasible itinerary found under given constraints."}))
        return

    # Choose one solution (first)
    sol = solutions[0]
    # Build order list by position
    ordered_cities = [sol[f"pos{i}"] for i in range(1, len(cities) + 1)]

    # Recompute start/end days for output
    start_day = {}
    end_day = {}
    current_start = 1
    for city in ordered_cities:
        start_day[city] = current_start
        end_day[city] = current_start + durations[city] - 1
        current_start = end_day[city]

    itinerary = []
    for city in ordered_cities:
        itinerary.append({
            "day_range": f"Day {start_day[city]}-{end_day[city]}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
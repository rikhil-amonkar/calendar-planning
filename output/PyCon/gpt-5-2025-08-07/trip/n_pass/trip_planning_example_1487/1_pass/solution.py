import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and required durations
    cities = [
        "Copenhagen", "Geneva", "Mykonos", "Naples", "Prague",
        "Dubrovnik", "Athens", "Santorini", "Brussels", "Munich"
    ]
    durations = {
        "Copenhagen": 5,
        "Geneva": 3,
        "Mykonos": 2,
        "Naples": 4,
        "Prague": 2,
        "Dubrovnik": 3,
        "Athens": 4,
        "Santorini": 5,
        "Brussels": 4,
        "Munich": 5,
    }

    # Direct flights (undirected)
    direct_pairs = [
        ("Copenhagen", "Dubrovnik"),
        ("Brussels", "Copenhagen"),
        ("Prague", "Geneva"),
        ("Athens", "Geneva"),
        ("Naples", "Dubrovnik"),
        ("Athens", "Dubrovnik"),
        ("Geneva", "Mykonos"),
        ("Naples", "Mykonos"),
        ("Naples", "Copenhagen"),
        ("Munich", "Mykonos"),
        ("Naples", "Athens"),
        ("Prague", "Athens"),
        ("Santorini", "Geneva"),
        ("Athens", "Santorini"),
        ("Naples", "Munich"),
        ("Prague", "Copenhagen"),
        ("Brussels", "Naples"),
        ("Athens", "Mykonos"),
        ("Athens", "Copenhagen"),
        ("Naples", "Geneva"),
        ("Dubrovnik", "Munich"),
        ("Brussels", "Munich"),
        ("Prague", "Brussels"),
        ("Brussels", "Athens"),
        ("Athens", "Munich"),
        ("Geneva", "Munich"),
        ("Copenhagen", "Munich"),
        ("Brussels", "Geneva"),
        ("Copenhagen", "Geneva"),
        ("Prague", "Munich"),
        ("Copenhagen", "Santorini"),
        ("Naples", "Santorini"),
        ("Geneva", "Dubrovnik"),
    ]
    flights = set()
    for a, b in direct_pairs:
        flights.add((a, b))
        flights.add((b, a))

    # Problem setup
    problem = Problem()

    # Variables: City at each position (0..9) and Start day for each position
    for i in range(10):
        problem.addVariable(f"City_{i}", cities)
        problem.addVariable(f"Start_{i}", range(1, 29))

    # All positions must contain different cities
    problem.addConstraint(AllDifferentConstraint(), [f"City_{i}" for i in range(10)])

    # Start day of first city must be Day 1
    problem.addConstraint(lambda s: s == 1, (f"Start_0",))

    # Enforce adjacency: direct flight and overlap of 1 day (travel day counted in both cities)
    for i in range(9):
        def adj(ci, cj, si, sj, durations=durations, flights=flights):
            return (ci, cj) in flights and (sj == si + durations[ci] - 1)
        problem.addConstraint(adj, (f"City_{i}", f"City_{i+1}", f"Start_{i}", f"Start_{i+1}"))

    # Fix Mykonos to be last and exactly days 27-28 (conference constraint)
    problem.addConstraint(lambda c: c == "Mykonos", (f"City_9",))
    problem.addConstraint(lambda s: s == 27, (f"Start_9",))

    # City-specific window constraints:
    # - Copenhagen (5 days) includes at least one day in 11..15
    # - Athens (4 days) includes at least one day in 8..11
    # - Naples (4 days) includes at least one day in 5..8
    # - Mykonos already fixed to 27..28 via Start_9, but also ensure any position respect 27..28 if Mykonos were elsewhere
    def city_window(city, start, durations=durations):
        if city == "Copenhagen":
            return start <= 15 and (start + durations[city] - 1) >= 11
        if city == "Athens":
            return start <= 11 and (start + durations[city] - 1) >= 8
        if city == "Naples":
            return start <= 8 and (start + durations[city] - 1) >= 5
        if city == "Mykonos":
            return start == 27  # reinforce exact conference days
        return True

    for i in range(10):
        problem.addConstraint(city_window, (f"City_{i}", f"Start_{i}"))

    # Solve
    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    # Build ordered itinerary
    itinerary = []
    for i in range(10):
        city = solution[f"City_{i}"]
        start = solution[f"Start_{i}"]
        end = start + durations[city] - 1
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
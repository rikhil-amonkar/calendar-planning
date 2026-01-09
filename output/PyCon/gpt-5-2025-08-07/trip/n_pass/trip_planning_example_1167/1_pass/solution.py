import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Cities and required stay durations (in days)
    durations = {
        "Dublin": 5,
        "Krakow": 4,
        "Istanbul": 3,
        "Venice": 3,
        "Naples": 4,
        "Brussels": 2,
        "Mykonos": 4,
        "Frankfurt": 3,
    }

    cities = list(durations.keys())

    # Directed flight edges: "A and B" => both directions; explicit one-way kept one-way
    edges = set()
    def add_undirected(a, b):
        edges.add((a, b))
        edges.add((b, a))

    # Add connections
    add_undirected("Dublin", "Brussels")
    add_undirected("Mykonos", "Naples")
    add_undirected("Venice", "Istanbul")
    add_undirected("Frankfurt", "Krakow")
    add_undirected("Naples", "Dublin")
    add_undirected("Krakow", "Brussels")
    add_undirected("Naples", "Istanbul")
    add_undirected("Naples", "Brussels")
    add_undirected("Istanbul", "Frankfurt")
    edges.add(("Brussels", "Frankfurt"))  # one-way as specified
    add_undirected("Istanbul", "Krakow")
    add_undirected("Istanbul", "Brussels")
    add_undirected("Venice", "Frankfurt")
    add_undirected("Naples", "Frankfurt")
    add_undirected("Dublin", "Krakow")
    add_undirected("Venice", "Brussels")
    add_undirected("Naples", "Venice")
    add_undirected("Istanbul", "Dublin")
    add_undirected("Venice", "Dublin")
    add_undirected("Dublin", "Frankfurt")

    # Problem setup
    problem = Problem()

    # Variables: order_1 .. order_8 (city names), s_1 .. s_8 (start days)
    order_vars = [f"order_{i}" for i in range(1, 9)]
    start_vars = [f"s_{i}" for i in range(1, 9)]

    # Domains
    for var in order_vars:
        problem.addVariable(var, cities)
    # Start day domains
    problem.addVariable("s_1", [1])  # trip starts day 1
    for i in range(2, 9):
        problem.addVariable(f"s_{i}", range(1, 22))  # 1..21

    # All cities must be visited exactly once
    problem.addConstraint(AllDifferentConstraint(), order_vars)

    # Sequential day-link constraints: s_i = s_{i-1} + d(order_{i-1}) - 1
    def link_constraint(prev_city, s_prev, s_curr):
        return s_curr == s_prev + durations[prev_city] - 1

    for i in range(2, 9):
        problem.addConstraint(
            link_constraint,
            (f"order_{i-1}", f"s_{i-1}", f"s_{i}")
        )

    # Flight adjacency constraints between consecutive cities
    def adjacency_ok(a, b):
        return (a, b) in edges

    for i in range(1, 8):
        problem.addConstraint(
            adjacency_ok,
            (f"order_{i}", f"order_{i+1}")
        )

    # City-specific date constraints:
    # - Dublin: attend show Day 11-15, and 5-day stay => start at 11 (ends 15)
    # - Mykonos: visit relatives between Day 1-4 and 4-day stay => start at 1 (ends 4)
    # - Frankfurt: meet friends between Day 15-17 and 3-day stay => start at 15 (ends 17)
    # - Istanbul: meet a friend between Day 9-11 => stay must overlap [9,11]
    def city_specific(city, s):
        # Dublin fixed window
        if city == "Dublin":
            return s == 11
        # Mykonos fixed window at trip start
        if city == "Mykonos":
            return s == 1
        # Frankfurt fixed window
        if city == "Frankfurt":
            return s == 15
        # Istanbul must overlap [9, 11]
        if city == "Istanbul":
            # 3-day stay starting s -> ends at s+2 must satisfy overlap
            return (s <= 11) and (s + 2 >= 9)
        # No special constraint for others
        return True

    for i in range(1, 9):
        problem.addConstraint(city_specific, (f"order_{i}", f"s_{i}"))

    # Solve
    solutions = problem.getSolutions()

    if not solutions:
        output = {"itinerary": []}
        print(json.dumps(output))
        return

    # Choose the first solution
    sol = solutions[0]

    # Build itinerary in order
    itinerary = []
    for i in range(1, 9):
        city = sol[f"order_{i}"]
        s = sol[f"s_{i}"]
        e = s + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
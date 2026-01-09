import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Cities and required durations (inclusive, counting overlap on flight days)
    cities = [
        "Stockholm", "Hamburg", "Florence", "Istanbul", "Oslo",
        "Vilnius", "Santorini", "Munich", "Frankfurt", "Krakow"
    ]
    durations = {
        "Stockholm": 3,
        "Hamburg": 5,
        "Florence": 2,
        "Istanbul": 5,
        "Oslo": 5,
        "Vilnius": 5,
        "Santorini": 2,
        "Munich": 5,
        "Frankfurt": 4,
        "Krakow": 5
    }

    total_days = 32  # Unique calendar days
    segments = len(cities)  # 10 cities -> 9 flights
    # Sum of durations must equal total_days + (segments - 1) because of overlap rule
    assert sum(durations.values()) == total_days + (segments - 1)

    # Directed flight edges
    edges = set()
    def add_undirected(a, b):
        edges.add((a, b))
        edges.add((b, a))
    def add_directed(a, b):
        edges.add((a, b))

    add_undirected("Oslo", "Stockholm")
    add_undirected("Krakow", "Frankfurt")
    add_undirected("Krakow", "Istanbul")
    add_undirected("Munich", "Stockholm")
    add_undirected("Hamburg", "Stockholm")
    add_directed("Krakow", "Vilnius")
    add_undirected("Oslo", "Istanbul")
    add_undirected("Istanbul", "Stockholm")
    add_undirected("Oslo", "Krakow")
    add_undirected("Vilnius", "Istanbul")
    add_undirected("Oslo", "Vilnius")
    add_undirected("Frankfurt", "Istanbul")
    add_undirected("Oslo", "Frankfurt")
    add_undirected("Munich", "Hamburg")
    add_undirected("Munich", "Istanbul")
    add_undirected("Oslo", "Munich")
    add_undirected("Frankfurt", "Florence")
    add_undirected("Oslo", "Hamburg")
    add_undirected("Vilnius", "Frankfurt")
    add_directed("Florence", "Munich")
    add_undirected("Krakow", "Munich")
    add_undirected("Hamburg", "Istanbul")
    add_undirected("Frankfurt", "Stockholm")
    add_directed("Stockholm", "Santorini")
    add_undirected("Frankfurt", "Munich")
    add_directed("Santorini", "Oslo")
    add_undirected("Krakow", "Stockholm")
    add_directed("Vilnius", "Munich")
    add_undirected("Frankfurt", "Hamburg")

    # Event constraints:
    # - Must be in Krakow from Day 5 to Day 9 (duration 5) => Krakow segment is exactly Day 5-9
    # - Must be in Istanbul from Day 25 to Day 29 (duration 5) => Istanbul segment is exactly Day 25-29
    krakow_required_start = 5
    istanbul_required_start = 25

    # Build constraint problem
    problem = Problem()
    # Variable: position of each city in itinerary order (0..9)
    for c in cities:
        problem.addVariable(c, range(len(cities)))

    # All positions must be unique
    problem.addConstraint(AllDifferentConstraint(), cities)

    # Disallow adjacency where a direct flight does not exist (A immediately before B)
    for a in cities:
        for b in cities:
            if a == b:
                continue
            if (a, b) not in edges:
                # If there is no direct flight from a to b, then a cannot be immediately before b
                problem.addConstraint(lambda pa, pb: pa + 1 != pb, (a, b))

    # Global constraint to enforce day-based requirements and sequencing semantics
    def global_itinerary_constraint(*positions):
        pos_map = dict(zip(cities, positions))
        # Build order by position
        order = sorted(cities, key=lambda c: pos_map[c])
        # Compute day ranges with overlap on transition days
        start_day = {}
        end_day = {}
        current_start = 1
        for c in order:
            s = current_start
            e = s + durations[c] - 1
            start_day[c] = s
            end_day[c] = e
            current_start = e  # Overlap: next segment starts on previous end day

        # Ensure last day aligns exactly with total_days
        if end_day[order[-1]] != total_days:
            return False

        # Enforce Krakow and Istanbul date constraints
        if start_day["Krakow"] != krakow_required_start:
            return False
        if start_day["Istanbul"] != istanbul_required_start:
            return False

        # Verify direct flights exist for all consecutive pairs (directional)
        for i in range(len(order) - 1):
            a, b = order[i], order[i + 1]
            if (a, b) not in edges:
                return False

        return True

    problem.addConstraint(global_itinerary_constraint, cities)

    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"itinerary": []}))
        return

    # Build ordered itinerary
    ordered_cities = sorted(cities, key=lambda c: solution[c])
    itinerary = []
    current_start = 1
    for c in ordered_cities:
        s = current_start
        e = s + durations[c] - 1
        itinerary.append({"day_range": f"Day {s}-{e}", "place": c})
        current_start = e

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
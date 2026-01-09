import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables and constraints
    total_days = 21
    cities = ["Manchester", "Istanbul", "Venice", "Krakow", "Lyon"]
    durations = {
        "Manchester": 3,
        "Istanbul": 7,
        "Venice": 7,
        "Krakow": 6,
        "Lyon": 2,
    }
    # Event windows (inclusive)
    windows = {
        "Manchester": (1, 3),  # Wedding between day 1 and 3
        "Venice": (3, 9),      # Workshop between day 3 and 9
    }
    # Direct-flight connections (undirected)
    direct_pairs = {
        frozenset(("Manchester", "Venice")),
        frozenset(("Manchester", "Istanbul")),
        frozenset(("Venice", "Istanbul")),
        frozenset(("Istanbul", "Krakow")),
        frozenset(("Venice", "Lyon")),
        frozenset(("Lyon", "Istanbul")),
        frozenset(("Manchester", "Krakow")),
    }

    def is_direct(a, b):
        return frozenset((a, b)) in direct_pairs

    def compute_schedule(order):
        # Build inclusive day ranges with 1-day overlaps between consecutive cities
        start = 1
        schedule = []
        for city in order:
            end = start + durations[city] - 1
            schedule.append((city, start, end))
            start = end  # overlap next start with this end (flight day)
        return schedule

    # Set up the constraint problem
    problem = Problem()
    pos_vars = ["pos1", "pos2", "pos3", "pos4", "pos5"]
    for v in pos_vars:
        problem.addVariable(v, cities)
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Custom constraint to enforce flight connectivity, event windows, and total days
    def itinerary_constraint(p1, p2, p3, p4, p5):
        order = [p1, p2, p3, p4, p5]
        # Enforce direct flights between consecutive cities
        for i in range(4):
            if not is_direct(order[i], order[i + 1]):
                return False

        schedule = compute_schedule(order)

        # Verify total covered days equals total_days (sum(durations) - overlaps)
        last_city, _, end_last = schedule[-1]
        if end_last != total_days:
            return False

        # Build quick lookup for city day ranges
        ranges = {city: (s, e) for city, s, e in schedule}

        # Enforce event window overlaps (must intersect)
        for city, (wa, wb) in windows.items():
            s, e = ranges[city]
            if e < wa or s > wb:
                return False

        return True

    problem.addConstraint(itinerary_constraint, pos_vars)

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        print(json.dumps({"itinerary": []}))
        return

    # Pick a deterministic solution (lexicographically by order tuple)
    def order_tuple(sol):
        return tuple(sol[v] for v in pos_vars)

    best = sorted(solutions, key=order_tuple)[0]
    order = [best[v] for v in pos_vars]

    # Build final itinerary with computed day ranges
    schedule = []
    start = 1
    for city in order:
        end = start + durations[city] - 1
        schedule.append({"day_range": f"Day {start}-{end}", "place": city})
        start = end  # overlap next start with this end

    output = {"itinerary": schedule}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()
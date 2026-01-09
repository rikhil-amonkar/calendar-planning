import json
import sys

# Ensure python-constraint is available
try:
    from constraint import Problem, AllDifferentConstraint
except ImportError:
    import subprocess
    subprocess.check_call([sys.executable, "-m", "pip", "install", "python-constraint"])
    from constraint import Problem, AllDifferentConstraint

def main():
    # Cities and required durations (in days, inclusive of travel overlap days)
    cities = ["Berlin", "Nice", "Athens", "Stockholm", "Barcelona", "Vilnius", "Lyon"]
    durations = {
        "Berlin": 3,
        "Nice": 5,
        "Athens": 5,
        "Stockholm": 5,
        "Barcelona": 2,
        "Vilnius": 4,
        "Lyon": 2,
    }
    total_days = 20

    # Direct flight connections (undirected)
    edges_list = [
        ("Lyon", "Nice"),
        ("Stockholm", "Athens"),
        ("Nice", "Athens"),
        ("Berlin", "Athens"),
        ("Berlin", "Nice"),
        ("Berlin", "Barcelona"),
        ("Berlin", "Vilnius"),
        ("Barcelona", "Nice"),
        ("Athens", "Vilnius"),
        ("Berlin", "Stockholm"),
        ("Nice", "Stockholm"),
        ("Barcelona", "Athens"),
        ("Barcelona", "Stockholm"),
        ("Barcelona", "Lyon"),
    ]
    edges = {frozenset(e) for e in edges_list}

    def adjacent(a, b):
        return frozenset({a, b}) in edges

    # CSP setup
    problem = Problem()

    # Variables: start day, end day, position in the visitation chain
    for c in cities:
        problem.addVariable(f"start_{c}", range(1, total_days + 1))
        problem.addVariable(f"end_{c}", range(1, total_days + 1))
        problem.addVariable(f"pos_{c}", range(1, len(cities) + 1))

    # Positions must be a permutation
    problem.addConstraint(AllDifferentConstraint(), [f"pos_{c}" for c in cities])

    # Duration constraints
    for c, d in durations.items():
        def dur_cons(s, e, d=d):
            return (e - s + 1) == d and s <= e
        problem.addConstraint(dur_cons, (f"start_{c}", f"end_{c}"))

    # Anchor chain to calendar: first city starts on Day 1, last city ends on Day 20
    n = len(cities)
    for c in cities:
        def anchor(pos, s, e):
            if pos == 1 and s != 1:
                return False
            if pos == n and e != total_days:
                return False
            return True
        problem.addConstraint(anchor, (f"pos_{c}", f"start_{c}", f"end_{c}"))

    # Consecutive chain continuity and direct flight adjacency
    # If A is immediately before B in the order, then:
    # - They must be connected by a direct flight
    # - start_B == end_A (overlap travel day counts for both)
    for A in cities:
        for B in cities:
            if A == B:
                continue
            def link(posA, posB, endA, startB, A=A, B=B):
                if posA + 1 == posB:
                    return adjacent(A, B) and (startB == endA)
                return True
            problem.addConstraint(link, (f"pos_{A}", f"pos_{B}", f"end_{A}", f"start_{B}"))

    # Event/day inclusion constraints
    # Berlin: conference on day 1 and day 3 -> Berlin must include days 1 and 3
    def includes_berlin(s, e):
        return (s <= 1 <= e) and (s <= 3 <= e)
    problem.addConstraint(includes_berlin, (f"start_Berlin", f"end_Berlin"))

    # Barcelona: workshop between day 3 and day 4 -> include days 3 and 4
    def includes_barcelona(s, e):
        return (s <= 3 <= e) and (s <= 4 <= e)
    problem.addConstraint(includes_barcelona, (f"start_Barcelona", f"end_Barcelona"))

    # Lyon: wedding between day 4 and day 5 -> include days 4 and 5
    def includes_lyon(s, e):
        return (s <= 4 <= e) and (s <= 5 <= e)
    problem.addConstraint(includes_lyon, (f"start_Lyon", f"end_Lyon"))

    # Solve
    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"itinerary": []}))
        return

    # Build itinerary sorted by start day
    itinerary_entries = []
    for c in cities:
        s = solution[f"start_{c}"]
        e = solution[f"end_{c}"]
        itinerary_entries.append((s, e, c))
    itinerary_entries.sort(key=lambda x: (x[0], x[1], x[2]))

    itinerary = []
    for s, e, c in itinerary_entries:
        itinerary.append({"day_range": f"Day {s}-{e}", "place": c})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
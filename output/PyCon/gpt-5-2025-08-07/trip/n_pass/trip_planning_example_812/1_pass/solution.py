import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Cities and required stay durations (days)
    durations = {
        "Paris": 5,
        "Florence": 3,
        "Vienna": 2,
        "Porto": 3,
        "Munich": 5,
        "Nice": 5,
        "Warsaw": 3,
    }

    total_days = 20
    cities = list(durations.keys())

    # Build directed flight adjacency based on provided direct flights
    edges = set()

    def add_bidirectional(a, b):
        edges.add((a, b))
        edges.add((b, a))

    def add_direct(a, b):
        edges.add((a, b))

    # Add edges
    add_bidirectional("Florence", "Vienna")
    add_bidirectional("Paris", "Warsaw")
    add_bidirectional("Munich", "Vienna")
    add_bidirectional("Porto", "Vienna")
    add_bidirectional("Warsaw", "Vienna")
    add_direct("Florence", "Munich")  # directional
    add_bidirectional("Munich", "Warsaw")
    add_bidirectional("Munich", "Nice")
    add_bidirectional("Paris", "Florence")
    add_bidirectional("Warsaw", "Nice")
    add_bidirectional("Porto", "Munich")
    add_bidirectional("Porto", "Nice")
    add_bidirectional("Paris", "Vienna")
    add_bidirectional("Nice", "Vienna")
    add_bidirectional("Porto", "Paris")
    add_bidirectional("Paris", "Nice")
    add_bidirectional("Paris", "Munich")
    add_bidirectional("Porto", "Warsaw")

    # Build CSP
    problem = Problem()

    # Variables for the order of the 7 cities (pos1..pos7)
    # Fix Porto to be first (must attend workshop days 1-3)
    problem.addVariable("pos1", ["Porto"])
    # Fix Vienna to be last (must visit relatives on days 19-20)
    problem.addVariable("pos7", ["Vienna"])

    middle_cities = [c for c in cities if c not in ("Porto", "Vienna")]
    for i in range(2, 7):
        problem.addVariable(f"pos{i}", middle_cities)

    # All cities must be visited exactly once
    problem.addConstraint(AllDifferentConstraint(), [f"pos{i}" for i in range(1, 8)])

    # Custom constraint to enforce flights, day overlaps, and event windows
    def itinerary_constraint(pos1, pos2, pos3, pos4, pos5, pos6, pos7):
        order = [pos1, pos2, pos3, pos4, pos5, pos6, pos7]

        # Check direct flight availability in travel direction between consecutive cities
        for i in range(len(order) - 1):
            if (order[i], order[i + 1]) not in edges:
                return False

        # Compute intervals with 1-day overlaps at each transition:
        # next city starts the same day the previous city ends
        intervals = {}  # city -> (start, end)
        current_start = 1
        for city in order:
            end = current_start + durations[city] - 1
            intervals[city] = (current_start, end)
            current_start = end  # 1-day overlap rule

        # Validate total span ends on day 20
        last_end = intervals[order[-1]][1]
        if last_end != total_days:
            return False

        # Event constraints:
        # Porto days 1-3
        s, e = intervals["Porto"]
        if not (s <= 1 and e >= 3):
            return False

        # Warsaw days 13-15 (wedding)
        s, e = intervals["Warsaw"]
        if not (s <= 13 and e >= 15):
            return False

        # Vienna days 19-20 (relatives)
        s, e = intervals["Vienna"]
        if not (s <= 19 and e >= 20):
            return False

        return True

    problem.addConstraint(
        itinerary_constraint,
        ["pos1", "pos2", "pos3", "pos4", "pos5", "pos6", "pos7"],
    )

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No feasible itinerary found with the given constraints.")

    # Choose a deterministic solution (lexicographically smallest order tuple)
    solutions.sort(key=lambda sol: tuple(sol[f"pos{i}"] for i in range(1, 8)))
    sol = solutions[0]
    order = [sol[f"pos{i}"] for i in range(1, 8)]

    # Recompute intervals for the chosen solution
    intervals = {}
    current_start = 1
    for city in order:
        end = current_start + durations[city] - 1
        intervals[city] = (current_start, end)
        current_start = end

    # Build itinerary output in visit order
    itinerary = []
    for city in order:
        s, e = intervals[city]
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
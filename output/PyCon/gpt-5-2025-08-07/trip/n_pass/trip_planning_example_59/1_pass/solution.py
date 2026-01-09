import json
import itertools
from constraint import Problem

def main():
    # Input variables (constraints)
    total_days = 16
    cities = ["Bucharest", "Lyon", "Porto"]
    required_days = {"Bucharest": 7, "Lyon": 7, "Porto": 4}
    # Direct flights (undirected)
    direct_edges = {("Bucharest", "Lyon"), ("Lyon", "Bucharest"),
                    ("Lyon", "Porto"), ("Porto", "Lyon")}
    # Wedding must be in Bucharest on a day within this inclusive window
    wedding_window = (1, 7)

    # Generate allowed routes: permutations of cities with only direct legs
    allowed_routes = []
    for route in itertools.permutations(cities, 3):
        if (route[0], route[1]) in direct_edges and (route[1], route[2]) in direct_edges:
            allowed_routes.append(route)

    # Build CSP
    problem = Problem()
    problem.addVariable("route_idx", list(range(len(allowed_routes))))
    problem.addVariable("t1", list(range(1, total_days + 1)))
    problem.addVariable("t2", list(range(1, total_days + 1)))

    def constraint_func(route_idx, t1, t2):
        # Ensure chronological order and valid bounds
        if not (1 <= t1 <= total_days and 1 <= t2 <= total_days and t1 <= t2):
            return False

        # Segment lengths (inclusive with overlap on flight days)
        l1 = t1  # days 1..t1
        l2 = t2 - t1 + 1  # days t1..t2
        l3 = (total_days + 1) - t2  # days t2..total_days

        if l1 <= 0 or l2 <= 0 or l3 <= 0:
            return False

        route = allowed_routes[route_idx]
        city_len = {
            route[0]: l1,
            route[1]: l2,
            route[2]: l3
        }

        # Enforce required days in each city
        for c in cities:
            if city_len.get(c, 0) != required_days[c]:
                return False

        # Wedding constraint: be in Bucharest on at least one day within [wedding_window]
        w_start, w_end = wedding_window
        # Determine Bucharest segment range
        if route[0] == "Bucharest":
            b_start, b_end = 1, t1
        elif route[1] == "Bucharest":
            b_start, b_end = t1, t2
        else:  # route[2] == "Bucharest"
            b_start, b_end = t2, total_days

        # Check intersection with wedding window
        if b_end < w_start or b_start > w_end:
            return False

        return True

    problem.addConstraint(constraint_func, ("route_idx", "t1", "t2"))

    solutions = problem.getSolutions()

    if not solutions:
        # If no solution found (should not happen for the given constraints), output empty itinerary
        print(json.dumps({"itinerary": []}))
        return

    # Choose an "optimal" solution: earliest possible Bucharest wedding day (then earliest flights)
    def score(sol):
        route = allowed_routes[sol["route_idx"]]
        t1, t2 = sol["t1"], sol["t2"]

        # Compute Bucharest presence range
        if route[0] == "Bucharest":
            b_start, b_end = 1, t1
        elif route[1] == "Bucharest":
            b_start, b_end = t1, t2
        else:
            b_start, b_end = t2, total_days

        w_days = range(wedding_window[0], wedding_window[1] + 1)
        buch_days = range(b_start, b_end + 1)
        common = sorted(set(w_days).intersection(buch_days))
        earliest_wedding_day = common[0] if common else 999

        return (earliest_wedding_day, sol["t1"], sol["t2"], allowed_routes[sol["route_idx"]])

    best = sorted(solutions, key=score)[0]

    # Build itinerary output with inclusive overlap on flight days
    route = allowed_routes[best["route_idx"]]
    t1, t2 = best["t1"], best["t2"]

    segments = [
        {"day_range": f"Day 1-{t1}", "place": route[0]},
        {"day_range": f"Day {t1}-{t2}", "place": route[1]},
        {"day_range": f"Day {t2}-{total_days}", "place": route[2]},
    ]

    print(json.dumps({"itinerary": segments}, ensure_ascii=False))

if __name__ == "__main__":
    main()
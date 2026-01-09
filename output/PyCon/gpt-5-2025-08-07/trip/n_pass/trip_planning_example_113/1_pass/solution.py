import json
import sys
import subprocess

# Ensure python-constraint is installed
try:
    from constraint import Problem, AllDifferentConstraint
except Exception:
    subprocess.run(
        [sys.executable, "-m", "pip", "install", "python-constraint", "--quiet"],
        check=True,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables (trip constraints)
    total_days = 12
    cities = ["Milan", "Naples", "Seville"]
    required_durations = {
        "Naples": 3,
        "Seville": 4,
        "Milan": 7,
    }
    # Direct flights (bidirectional)
    direct_routes = {
        ("Milan", "Seville"), ("Seville", "Milan"),
        ("Naples", "Milan"), ("Milan", "Naples")
    }
    # Event constraint: must be in Seville from day 9 to day 12
    show_city = "Seville"
    show_start = 9
    show_end = 12

    # Setup constraint problem
    problem = Problem()
    # Order of visiting the three cities
    problem.addVariables(["C1", "C2", "C3"], cities)
    problem.addConstraint(AllDifferentConstraint(), ["C1", "C2", "C3"])
    # Boundary days where flights occur (overlap days count for both cities)
    # City 1: Day 1 .. D1
    # City 2: Day D1 .. D2
    # City 3: Day D2 .. total_days
    problem.addVariable("D1", range(1, total_days + 1))
    problem.addVariable("D2", range(1, total_days + 1))
    problem.addConstraint(lambda d1, d2: d1 <= d2, ("D1", "D2"))

    # Direct flight constraints
    problem.addConstraint(lambda c1, c2: (c1, c2) in direct_routes, ("C1", "C2"))
    problem.addConstraint(lambda c2, c3: (c2, c3) in direct_routes, ("C2", "C3"))

    # Duration and event constraints integrated
    def durations_and_event(c1, c2, c3, d1, d2):
        # Compute durations with overlap on flight days
        durations = {
            c1: d1,                 # Days 1..d1
            c2: d2 - d1 + 1,        # Days d1..d2
            c3: total_days - d2 + 1 # Days d2..total_days
        }
        # Check required durations for each city
        for city, req in required_durations.items():
            if durations.get(city, -1) != req:
                return False

        # Ensure show_city covers the full [show_start, show_end] range
        if show_city == c1:
            seg_start, seg_end = 1, d1
        elif show_city == c2:
            seg_start, seg_end = d1, d2
        else:  # show_city == c3
            seg_start, seg_end = d2, total_days

        if not (seg_start <= show_start and seg_end >= show_end):
            return False

        return True

    problem.addConstraint(durations_and_event, ("C1", "C2", "C3", "D1", "D2"))

    # Solve
    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"error": "No feasible itinerary found given the constraints."}))
        return

    c1, c2, c3 = solution["C1"], solution["C2"], solution["C3"]
    d1, d2 = solution["D1"], solution["D2"]

    itinerary = [
        {"day_range": f"Day 1-{d1}", "place": c1},
        {"day_range": f"Day {d1}-{d2}", "place": c2},
        {"day_range": f"Day {d2}-{total_days}", "place": c3},
    ]

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables and constraints
    total_days = 17
    cities = ["Seville", "Vilnius", "Santorini", "London", "Stuttgart", "Dublin", "Frankfurt"]

    # Required stay durations (days in each city)
    durations = {
        "Seville": 5,
        "Vilnius": 3,
        "Santorini": 2,
        "London": 2,
        "Stuttgart": 3,
        "Dublin": 3,
        "Frankfurt": 5,
    }

    # Direct flight connections (undirected)
    direct_flights = {
        frozenset(["Frankfurt", "Dublin"]),
        frozenset(["Frankfurt", "London"]),
        frozenset(["London", "Dublin"]),
        frozenset(["Vilnius", "Frankfurt"]),
        frozenset(["Frankfurt", "Stuttgart"]),
        frozenset(["Dublin", "Seville"]),
        frozenset(["London", "Santorini"]),
        frozenset(["Stuttgart", "London"]),
        frozenset(["Santorini", "Dublin"]),
    }

    # Fixed day constraints:
    # - Be in London on days 9-10 (start=9, duration=2)
    # - Be in Stuttgart on days 7-9 (start=7, duration=3)
    london_start_day = 9
    stuttgart_start_day = 7

    # Set up the constraint problem
    problem = Problem()

    # Variables: position 1..7 -> city at that position (permutation)
    pos_vars = [f"pos{i}" for i in range(1, 8)]
    for var in pos_vars:
        problem.addVariable(var, cities)

    # All positions must be assigned different cities
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Consecutive positions must have a direct flight
    def adjacent_direct(c1, c2):
        return frozenset([c1, c2]) in direct_flights

    for i in range(1, 7):
        problem.addConstraint(adjacent_direct, (f"pos{i}", f"pos{i+1}"))

    # Enforce day-specific placement using the overlap rule:
    # For a chain of cities with overlaps on transition days:
    # start(pos1)=1; start(pos_{k+1}) = end(pos_k) = start(pos_k) + duration(pos_k) - 1
    # So: start(pos_k) = 1 + sum_{i<k} (duration(pos_i) - 1)
    # We must have start(London)=9 and start(Stuttgart)=7
    def day_constraints(*assigned):
        order = list(assigned)  # [pos1, pos2, ..., pos7]
        # Compute start days by chain rule
        start_day = {}
        s = 1
        for city in order:
            start_day[city] = s
            s = s + durations[city] - 1  # next starts at end(current) due to overlap

        # Check London and Stuttgart placement
        if start_day.get("London") != london_start_day:
            return False
        if start_day.get("Stuttgart") != stuttgart_start_day:
            return False

        # Also ensure the chain exactly covers total_days:
        # With s1=1, end(last) = 1 + sum(d-1) = 17 (since durations are fixed to sum 23)
        # Still assert for robustness
        last_city = order[-1]
        end_last = start_day[last_city] + durations[last_city] - 1
        return end_last == total_days

    problem.addConstraint(day_constraints, tuple(pos_vars))

    # Solve
    solutions = problem.getSolutions()

    if not solutions:
        # Fallback JSON in case of no solution (should not happen with given constraints)
        print(json.dumps({"itinerary": []}))
        return

    # Choose the first solution deterministically by sorting on the tuple of positions
    def solution_key(sol):
        return tuple(sol[f"pos{i}"] for i in range(1, 8))

    solution = sorted(solutions, key=solution_key)[0]

    # Build the itinerary with overlapping day ranges
    itinerary = []
    current_start = 1
    for i in range(1, 8):
        city = solution[f"pos{i}"]
        start = current_start
        end = start + durations[city] - 1
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
        current_start = end  # Next city starts at end (overlapping transition day)

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
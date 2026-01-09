import json
from constraint import Problem

def main():
    # Input variables (cities and constraints)
    cities = ["Split", "Helsinki", "Reykjavik", "Vilnius", "Geneva"]
    required_days = {
        "Split": 2,
        "Helsinki": 2,
        "Reykjavik": 3,
        "Vilnius": 3,
        "Geneva": 6,
    }
    # Direct flight pairs (undirected)
    direct_pairs = [
        ("Split", "Helsinki"),
        ("Geneva", "Split"),
        ("Geneva", "Helsinki"),
        ("Helsinki", "Reykjavik"),
        ("Vilnius", "Helsinki"),
        ("Split", "Vilnius"),
    ]
    direct_edges = {frozenset(pair) for pair in direct_pairs}

    total_days = 12
    vilnius_window = [7, 8, 9]    # must be in Vilnius on these days
    reykjavik_window = [10, 11, 12]  # must be in Reykjavik on these days

    # Create a CSP problem
    problem = Problem()

    # Variables: L0 (start location before Day 1), and L1..L12 (end-of-day locations)
    var_names = [f"L{i}" for i in range(0, total_days + 1)]
    for name in var_names:
        problem.addVariable(name, cities)

    # Constraint: No flight on Day 1 start -> end to avoid day-1 double counting ambiguity
    problem.addConstraint(lambda a, b: a == b, ("L0", "L1"))

    # Constraint: If there is a flight on day d (L_{d-1} != L_d), it must be a direct flight
    for d in range(1, total_days + 1):
        problem.addConstraint(
            lambda prev, curr, edges=direct_edges: (prev == curr) or (frozenset({prev, curr}) in edges),
            (f"L{d-1}", f"L{d}")
        )

    # Global constraint to enforce city-day counts and presence windows
    def global_constraint(*vals):
        # vals correspond to L0..L12 in order
        L = {i: vals[i] for i in range(total_days + 1)}

        # Helper to determine if 'city' is counted on 'day'
        def present(city, day):
            if L[day] == city:
                return True
            if L[day - 1] == city and L[day - 1] != L[day]:
                return True
            return False

        # Compute counts with flight-day double counting
        counts = {c: 0 for c in cities}
        for d in range(1, total_days + 1):
            # end-of-day city counts for that day
            counts[L[d]] += 1
            # departure city's day also counts if a flight occurs
            if L[d - 1] != L[d]:
                counts[L[d - 1]] += 1

        # Enforce exact required days per city
        for c, req in required_days.items():
            if counts.get(c, 0) != req:
                return False

        # Enforce presence windows
        for d in vilnius_window:
            if not present("Vilnius", d):
                return False
        for d in reykjavik_window:
            if not present("Reykjavik", d):
                return False

        return True

    problem.addConstraint(global_constraint, var_names)

    # Solve
    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    # Build overlapping itinerary segments:
    # If L_{d-1} != L_d, day d appears in both the segment ending at day d (previous city)
    # and the segment starting at day d (new city).
    days = {i: solution[f"L{i}"] for i in range(0, total_days + 1)}

    segments = []
    current_city = days[1]
    start_day = 1
    for d in range(2, total_days + 1):
        if days[d] != current_city:
            # Close current segment at day d (inclusive)
            segments.append({
                "day_range": f"Day {start_day}-{d}",
                "place": current_city
            })
            # Start new segment at day d
            current_city = days[d]
            start_day = d
    # Close the last segment
    segments.append({
        "day_range": f"Day {start_day}-{total_days}",
        "place": current_city
    })

    # Output JSON
    print(json.dumps({"itinerary": segments}, ensure_ascii=False))

if __name__ == "__main__":
    main()
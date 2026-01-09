import json
from constraint import Problem

def main():
    # Input variables and parameters
    total_days = 15
    days = list(range(1, total_days + 1))
    cities = ["Paris", "Madrid", "Bucharest", "Seville"]

    # Required exact durations (counts of days present in each city, counting travel days for both origin and destination)
    required_durations = {
        "Paris": 6,
        "Madrid": 7,
        "Bucharest": 2,
        "Seville": 3,
    }

    # Direct flight pairs (undirected given, convert to directed)
    undirected_pairs = [
        ("Paris", "Bucharest"),
        ("Seville", "Paris"),
        ("Madrid", "Bucharest"),
        ("Madrid", "Paris"),
        ("Madrid", "Seville"),
    ]
    allowed_directed = set()
    for a, b in undirected_pairs:
        allowed_directed.add((a, b))
        allowed_directed.add((b, a))

    # Create CSP
    problem = Problem()

    # Variables: start and end city for each day (start in morning, end in evening)
    for d in days:
        problem.addVariable(f"S_{d}", cities)
        problem.addVariable(f"E_{d}", cities)

    # Constraint: Each day's transition is either staying (S == E) or a direct flight (S -> E allowed)
    def pair_ok(s, e):
        return (s == e) or ((s, e) in allowed_directed)

    for d in days:
        problem.addConstraint(pair_ok, (f"S_{d}", f"E_{d}"))

    # Continuity: The next day's start city must equal previous day's end city
    for d in range(2, total_days + 1):
        problem.addConstraint(lambda e_prev, s_curr: e_prev == s_curr, (f"E_{d-1}", f"S_{d}"))

    # Presence constraints:
    # Days 1-7: Must be present in Madrid each day (either starting or ending there on that day)
    for d in range(1, 8):
        problem.addConstraint(lambda s, e: (s == "Madrid") or (e == "Madrid"), (f"S_{d}", f"E_{d}"))

    # Days 14-15: Must be present in Bucharest each day
    for d in range(14, 16):
        problem.addConstraint(lambda s, e: (s == "Bucharest") or (e == "Bucharest"), (f"S_{d}", f"E_{d}"))

    # Global constraint: Exact durations per city (accounting for travel day presence in both cities)
    var_names = []
    for d in days:
        var_names.append(f"S_{d}")
        var_names.append(f"E_{d}")

    def durations_constraint(*vals):
        presence = {c: 0 for c in cities}
        # vals are ordered as [S_1, E_1, S_2, E_2, ..., S_15, E_15]
        for i in range(0, len(vals), 2):
            s = vals[i]
            e = vals[i + 1]
            if s == e:
                presence[s] += 1
            else:
                presence[s] += 1
                presence[e] += 1
        return all(presence[c] == required_durations[c] for c in cities)

    problem.addConstraint(durations_constraint, var_names)

    # Solve. If multiple, choose one with lexicographically earliest flight days.
    solutions = problem.getSolutions()

    if not solutions:
        print(json.dumps({"itinerary": []}))
        return

    def flight_days(sol):
        fdays = []
        for d in days:
            if sol[f"S_{d}"] != sol[f"E_{d}"]:
                fdays.append(d)
        return tuple(fdays)

    # Prefer solutions with minimal flights (implicitly 3 due to durations), then earliest flight days
    best_solution = min(solutions, key=lambda sol: (len(flight_days(sol)), flight_days(sol)))

    # Build itinerary segments as chronological ranges.
    # A travel day (S != E) is included as the last day of the origin segment and the first day of the destination segment.
    segments = []
    current_city = best_solution["S_1"]
    current_start = 1

    for d in days:
        s = best_solution[f"S_{d}"]
        e = best_solution[f"E_{d}"]
        if d == 1:
            current_city = s
            current_start = 1
        if s != e:
            # Close current segment at day d (includes travel day)
            segments.append({"day_range": f"Day {current_start}-{d}", "place": current_city})
            # Start a new segment at day d for destination city
            current_city = e
            current_start = d

    # Close final segment at day 15
    if segments:
        last_seg_end = int(segments[-1]["day_range"].split("-")[-1])
        if last_seg_end < total_days:
            segments.append({"day_range": f"Day {current_start}-{total_days}", "place": current_city})
    else:
        # No travel at all; single segment
        segments.append({"day_range": f"Day 1-{total_days}", "place": current_city})

    # Output JSON
    print(json.dumps({"itinerary": segments}, ensure_ascii=False))

if __name__ == "__main__":
    main()
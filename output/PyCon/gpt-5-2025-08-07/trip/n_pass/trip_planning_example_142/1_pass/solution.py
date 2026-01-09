import json
import sys
import subprocess

# Ensure python-constraint is available
try:
    from constraint import Problem
except ImportError:
    subprocess.run([sys.executable, "-m", "pip", "install", "python-constraint", "-q"], check=True)
    from constraint import Problem

def main():
    # Input variables (constraints)
    total_days = 7
    cities = ["Madrid", "Dublin", "Tallinn"]
    required_days = {
        "Madrid": 4,
        "Dublin": 3,
        "Tallinn": 2
    }
    # Allowed direct flights (both directions)
    direct_flights = {
        ("Madrid", "Dublin"), ("Dublin", "Madrid"),
        ("Dublin", "Tallinn"), ("Tallinn", "Dublin")
    }
    # Workshop presence required on these days (inclusive)
    workshop_presence_days = [6, 7]
    # Solver setup
    problem = Problem()
    days = list(range(1, total_days + 1))

    # Variables: Morning and End-of-day city for each day
    for d in days:
        problem.addVariable(f"M_{d}", cities)
        problem.addVariable(f"E_{d}", cities)

    # Constraint: Each day's end-of-day city is either same as morning (no flight) or reachable by direct flight
    def adjacency_ok(m, e):
        return (e == m) or ((m, e) in direct_flights)

    for d in days:
        problem.addConstraint(adjacency_ok, (f"M_{d}", f"E_{d}"))

    # Constraint: Next day's morning city equals previous day's end-of-day city
    for d in days[:-1]:
        problem.addConstraint(lambda e_prev, m_next: e_prev == m_next, (f"E_{d}", f"M_{d+1}"))

    # Constraint: Workshop presence in Tallinn on specified days
    for wd in workshop_presence_days:
        problem.addConstraint(lambda m, e: (m == "Tallinn") or (e == "Tallinn"), (f"M_{wd}", f"E_{wd}"))

    # Global counts constraint: counts of days present per city (presence on a flight day counts for both)
    # We pass variables in the order M_1,E_1,M_2,E_2,... so we can compute per-day presence
    var_order = []
    for d in days:
        var_order.append(f"M_{d}")
        var_order.append(f"E_{d}")

    def counts_constraint(*vals):
        counts = {c: 0 for c in cities}
        # vals = [M_1, E_1, M_2, E_2, ..., M_7, E_7]
        for i in range(0, len(vals), 2):
            m = vals[i]
            e = vals[i + 1]
            # Presence on a day counts once per city even if both m and e are that city
            for c in cities:
                if m == c or e == c:
                    counts[c] += 1
        return all(counts[c] == required_days[c] for c in cities)

    problem.addConstraint(counts_constraint, tuple(var_order))

    # Solve
    solutions = problem.getSolutions()

    if not solutions:
        print(json.dumps({"error": "No feasible itinerary found given the constraints."}))
        return

    # Choose an "optimal" solution:
    # 1) Prefer itineraries starting in Madrid if available
    # 2) Minimize travel days lexicographically (earlier flights)
    # 3) Tie-break by lexicographic order of morning cities sequence
    def travel_days(sol):
        return sorted(d for d in days if sol[f"M_{d}"] != sol[f"E_{d}"])

    def morning_seq(sol):
        return [cities.index(sol[f"M_{d}"]) for d in days]

    preferred = [s for s in solutions if s["M_1"] == "Madrid"]
    candidate_pool = preferred if preferred else solutions
    best_solution = min(candidate_pool, key=lambda s: (travel_days(s), morning_seq(s)))

    # Build itinerary as day ranges for presence in each city
    presence_by_city = {c: set() for c in cities}
    for d in days:
        m = best_solution[f"M_{d}"]
        e = best_solution[f"E_{d}"]
        presence_by_city[m].add(d)
        presence_by_city[e].add(d)

    def to_ranges(sorted_days_list):
        if not sorted_days_list:
            return []
        ranges = []
        start = prev = sorted_days_list[0]
        for x in sorted_days_list[1:]:
            if x == prev + 1:
                prev = x
            else:
                ranges.append((start, prev))
                start = prev = x
        ranges.append((start, prev))
        return ranges

    items = []
    for c in cities:
        ds = sorted(presence_by_city[c])
        for (s, e) in to_ranges(ds):
            items.append({"start": s, "end": e, "place": c})

    # Sort itinerary ranges by start day
    items.sort(key=lambda x: (x["start"], x["end"]))

    # Format output
    itinerary = [{"day_range": f"Day {it['start']}-{it['end']}", "place": it["place"]} for it in items]

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
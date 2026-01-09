import json
from constraint import Problem

def main():
    # Input variables (trip constraints)
    days = list(range(1, 9))  # 8 days
    cities = ["Prague", "Stuttgart", "Split", "Krakow", "Florence"]

    # Required total presence (day counts) per city
    required_city_days = {
        "Prague": 4,
        "Stuttgart": 2,
        "Split": 2,
        "Krakow": 2,
        "Florence": 2,
    }

    # Direct flight connections (undirected)
    direct_pairs = {
        frozenset(["Stuttgart", "Split"]),
        frozenset(["Prague", "Florence"]),
        frozenset(["Krakow", "Stuttgart"]),
        frozenset(["Krakow", "Split"]),
        frozenset(["Split", "Prague"]),
        frozenset(["Krakow", "Prague"]),
    }

    # Helper to check if a commute is allowed (same city or direct flight)
    def commute_ok(m, e):
        return (m == e) or (frozenset([m, e]) in direct_pairs)

    problem = Problem()

    # Variables: Morning (M) and Evening (E) city for each day
    M_vars = [f"M{d}" for d in days]
    E_vars = [f"E{d}" for d in days]
    for var in M_vars + E_vars:
        problem.addVariable(var, cities)

    # Continuity: Evening of day d equals Morning of day d+1
    for d in range(1, 8):
        problem.addConstraint(lambda e, m: e == m, (f"E{d}", f"M{d+1}"))

    # Only direct flights between different cities in a day
    for d in days:
        problem.addConstraint(lambda m, e: commute_ok(m, e), (f"M{d}", f"E{d}"))

    # Wedding in Stuttgart between day 2 and day 3
    problem.addConstraint(lambda x: x == "Stuttgart", ("E2",))
    problem.addConstraint(lambda x: x == "Stuttgart", ("M3",))

    # Meet friends in Split between day 3 and day 4
    problem.addConstraint(lambda x: x == "Split", ("E3",))
    problem.addConstraint(lambda x: x == "Split", ("M4",))

    # Logical deductions from exact day counts + event constraints:
    # Split must appear only on days 3 and 4 (exactly two days required, already occupied by meet constraint)
    for d in days:
        if d not in (3, 4):
            problem.addConstraint(lambda c: c != "Split", (f"M{d}",))
            problem.addConstraint(lambda c: c != "Split", (f"E{d}",))

    # Stuttgart appears only on days 2 and 3 (exactly two days required, already occupied by wedding constraint)
    for d in days:
        if d not in (2, 3):
            problem.addConstraint(lambda c: c != "Stuttgart", (f"M{d}",))
            problem.addConstraint(lambda c: c != "Stuttgart", (f"E{d}",))

    # Global constraint: exact city-day counts and exact number of flight days
    all_vars = M_vars + E_vars

    def global_counts_constraint(*vals):
        # Map variable names to values
        assignment = {var: val for var, val in zip(all_vars, vals)}
        # Compute presence per day as set of distinct cities present that day
        presence_by_city = {c: 0 for c in cities}
        flight_days = 0
        for d in days:
            m = assignment[f"M{d}"]
            e = assignment[f"E{d}"]
            if m != e:
                flight_days += 1
                presence_set = {m, e}
            else:
                presence_set = {m}
            for city in presence_set:
                presence_by_city[city] += 1

        # Check required totals
        for city, needed in required_city_days.items():
            if presence_by_city.get(city, 0) != needed:
                return False

        # Presence-days identity: total presence = 8 + number of flight days
        # With required totals summing to 12, flight_days must be exactly 4
        if flight_days != (sum(required_city_days.values()) - len(days)):
            return False

        return True

    problem.addConstraint(global_counts_constraint, tuple(all_vars))

    # Solve
    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"error": "No feasible itinerary found given the constraints."}))
        return

    # Build presence days per city
    city_days = {c: [] for c in cities}
    for d in days:
        m = solution[f"M{d}"]
        e = solution[f"E{d}"]
        if m == e:
            city_days[m].append(d)
        else:
            city_days[m].append(d)
            city_days[e].append(d)

    # Merge consecutive days into ranges for each city
    def merge_ranges(sorted_days):
        if not sorted_days:
            return []
        ranges = []
        start = prev = sorted_days[0]
        for day in sorted_days[1:]:
            if day == prev + 1:
                prev = day
            else:
                ranges.append((start, prev))
                start = prev = day
        ranges.append((start, prev))
        return ranges

    itinerary_segments = []
    for city in cities:
        dlist = sorted(set(city_days[city]))
        ranges = merge_ranges(dlist)
        for (a, b) in ranges:
            if a == b:
                dr = f"Day {a}"
            else:
                dr = f"Day {a}-{b}"
            itinerary_segments.append({"day_range": dr, "place": city})

    # Sort segments by start day for chronological output
    def range_start(seg):
        # Extract first number after "Day "
        dr = seg["day_range"].replace("Day ", "")
        start_str = dr.split("-")[0]
        return int(start_str)

    itinerary_segments.sort(key=range_start)

    # Output JSON
    print(json.dumps({"itinerary": itinerary_segments}, ensure_ascii=False))

if __name__ == "__main__":
    main()
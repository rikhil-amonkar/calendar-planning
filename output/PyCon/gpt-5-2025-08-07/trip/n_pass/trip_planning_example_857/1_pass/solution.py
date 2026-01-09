import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and required stay durations
    cities = ["Porto", "Geneva", "Mykonos", "Manchester", "Hamburg", "Naples", "Frankfurt"]
    durations = {
        "Porto": 2,
        "Geneva": 3,
        "Mykonos": 3,
        "Manchester": 4,
        "Hamburg": 5,
        "Naples": 5,
        "Frankfurt": 2,
    }
    total_days = 18

    # Direct flights (treated as undirected)
    flight_pairs = [
        ("Hamburg", "Frankfurt"),
        ("Naples", "Mykonos"),
        ("Hamburg", "Porto"),
        ("Hamburg", "Geneva"),  # "from Hamburg to Geneva" treated as undirected
        ("Mykonos", "Geneva"),
        ("Frankfurt", "Geneva"),
        ("Frankfurt", "Porto"),
        ("Geneva", "Porto"),
        ("Geneva", "Manchester"),
        ("Naples", "Manchester"),
        ("Frankfurt", "Naples"),
        ("Frankfurt", "Manchester"),
        ("Naples", "Geneva"),
        ("Porto", "Manchester"),
        ("Hamburg", "Manchester"),
    ]
    flights = set(frozenset(p) for p in flight_pairs)

    # Helper to compute itinerary from position mapping
    def compute_itinerary(pos_map):
        # Sort cities by their position (1..7)
        ordered = sorted(cities, key=lambda c: pos_map[c])
        # Build segments with overlapping flight days (start of next == end of current)
        start = 1
        segments = []
        for c in ordered:
            end = start + durations[c] - 1
            segments.append((c, start, end))
            start = end  # overlap next city's start on the same day (flight day)
        return segments

    # Constraint function to enforce all rules
    def itinerary_constraint(*pos_values):
        pos_map = {city: pos for city, pos in zip(cities, pos_values)}
        # All positions must be a permutation of 1..7 (AllDifferent ensures uniqueness)
        # Compute segments
        segments = compute_itinerary(pos_map)

        # Ensure consecutive cities are connected by direct flights
        for i in range(len(segments) - 1):
            a, _, _ = segments[i]
            b, _, _ = segments[i + 1]
            if frozenset({a, b}) not in flights:
                return False

        # Check overall days coverage
        first_start = segments[0][1]
        last_end = segments[-1][2]
        if first_start != 1 or last_end != total_days:
            return False

        # Extract start/end per city
        city_ranges = {c: (s, e) for (c, s, e) in segments}

        # Duration check (redundant by construction, but keep for safety)
        for c, (s, e) in city_ranges.items():
            if e - s + 1 != durations[c]:
                return False

        # Specific day/window constraints:
        # Frankfurt: attend annual show on days 5-6 -> must be exactly days 5-6 (since duration is 2)
        f_s, f_e = city_ranges["Frankfurt"]
        if not (f_s == 5 and f_e == 6):
            return False

        # Mykonos: meet friend between day 10 and 12 -> 3 days -> exactly 10-12
        m_s, m_e = city_ranges["Mykonos"]
        if not (m_s == 10 and m_e == 12):
            return False

        # Manchester: wedding between day 15 and 18 -> 4 days -> exactly 15-18
        man_s, man_e = city_ranges["Manchester"]
        if not (man_s == 15 and man_e == 18):
            return False

        # All other city stays are as specified by duration; no further constraints needed
        return True

    # Build CSP
    problem = Problem()
    # Variables: position of each city in the 7-stop itinerary
    for c in cities:
        problem.addVariable(c, range(1, len(cities) + 1))
    problem.addConstraint(AllDifferentConstraint(), cities)
    problem.addConstraint(itinerary_constraint, cities)

    solutions = problem.getSolutions()

    if not solutions:
        print(json.dumps({"itinerary": []}))
        return

    # Select one solution (any valid one)
    sol = solutions[0]
    # Build final itinerary
    segments = sorted(
        [(c, sol[c]) for c in cities],
        key=lambda x: x[1]
    )
    # Recompute exact day ranges for output
    start = 1
    itinerary_list = []
    for c, _ in segments:
        end = start + durations[c] - 1
        itinerary_list.append({
            "day_range": f"Day {start}-{end}",
            "place": c
        })
        start = end  # overlap

    print(json.dumps({"itinerary": itinerary_list}, ensure_ascii=False))

if __name__ == "__main__":
    main()
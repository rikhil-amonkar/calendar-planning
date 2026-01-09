import json
from constraint import Problem

def main():
    # Define cities and constraints
    cities = ["Frankfurt", "Naples", "Helsinki", "Lyon", "Prague"]
    required_days = {
        "Frankfurt": 3,
        "Naples": 4,
        "Helsinki": 4,
        "Lyon": 3,
        "Prague": 2,
    }
    total_days = 12
    # Direct flight edges (undirected)
    direct_pairs = {
        frozenset(("Prague", "Lyon")),
        frozenset(("Prague", "Frankfurt")),
        frozenset(("Frankfurt", "Lyon")),
        frozenset(("Helsinki", "Naples")),
        frozenset(("Helsinki", "Frankfurt")),
        frozenset(("Naples", "Frankfurt")),
        frozenset(("Prague", "Helsinki")),
    }

    # Helper to add presence constraint for a city on a given day
    def presence_constraint_city_on_day(city, day):
        # For day d in 1..11: present if M_d == city or (F_d == 1 and M_{d+1} == city)
        # For day 12: present if M_12 == city
        if day <= total_days - 1:
            def _c(m_d, f_d, m_next):
                return (m_d == city) or (f_d == 1 and m_next == city)
            return _c, [f"M{day}", f"F{day}", f"M{day+1}"]
        else:  # day 12
            def _c(m_d):
                return (m_d == city)
            return _c, [f"M{day}"]

    problem = Problem()

    # Add variables for morning city each day M1..M12
    for d in range(1, total_days + 1):
        problem.addVariable(f"M{d}", cities)

    # Add variables for flight indicator each day F1..F11 (no F12 to avoid M13)
    for d in range(1, total_days):
        problem.addVariable(f"F{d}", [0, 1])

    # Movement constraints: if no flight, stay; if flight, must move via direct edge
    def move_constraint(m_d, m_next, f_d):
        if f_d == 0:
            return m_next == m_d
        else:
            return (m_d != m_next) and (frozenset((m_d, m_next)) in direct_pairs)

    for d in range(1, total_days):
        problem.addConstraint(move_constraint, [f"M{d}", f"M{d+1}", f"F{d}"])

    # Fix Day 1 morning in Prague (natural start due to workshop)
    problem.addConstraint(lambda m1: m1 == "Prague", ["M1"])

    # Require presence in Prague on Day 1 and Day 2 (workshop)
    c_fn, vars_ = presence_constraint_city_on_day("Prague", 1)
    problem.addConstraint(c_fn, vars_)
    c_fn, vars_ = presence_constraint_city_on_day("Prague", 2)
    problem.addConstraint(c_fn, vars_)

    # Require presence in Helsinki from Day 2 to Day 5 (show)
    for d in range(2, 6):
        c_fn, vars_ = presence_constraint_city_on_day("Helsinki", d)
        problem.addConstraint(c_fn, vars_)

    # Exactly 4 flight days (since total counted city-days = 16 and unique days = 12)
    def flight_count_constraint(*fvals):
        return sum(fvals) == 4
    problem.addConstraint(flight_count_constraint, [f"F{d}" for d in range(1, total_days)])

    # Exact per-city day counts using presence (OR of morning city and destination on flight day)
    def exact_counts_constraint(*vals):
        # vals correspond to var_names order: M1..M12, F1..F11
        var_names = [f"M{d}" for d in range(1, total_days + 1)] + [f"F{d}" for d in range(1, total_days)]
        assignment = dict(zip(var_names, vals))

        # Compute presence counts
        counts = {c: 0 for c in cities}
        for d in range(1, total_days + 1):
            present = set()
            m_d = assignment[f"M{d}"]
            present.add(m_d)
            if d <= total_days - 1 and assignment[f"F{d}"] == 1:
                m_next = assignment[f"M{d+1}"]
                present.add(m_next)
            for c in present:
                counts[c] += 1

        # Check exact counts
        for c, req in required_days.items():
            if counts[c] != req:
                return False
        return True

    problem.addConstraint(
        exact_counts_constraint,
        [f"M{d}" for d in range(1, total_days + 1)] + [f"F{d}" for d in range(1, total_days)]
    )

    # Solve for one feasible itinerary
    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"itinerary": []}))
        return

    # Build day-by-day morning cities and flights
    M = [solution[f"M{d}"] for d in range(1, total_days + 1)]
    F = [solution[f"F{d}"] for d in range(1, total_days)]  # F[0] corresponds to Day 1

    # Build itinerary segments with overlap on flight days:
    # When flight on day d (M[d] -> M[d+1]), close previous segment at day d,
    # start next segment at day d (overlap).
    segments = []
    current_city = M[0]
    current_start = 1
    for d in range(1, total_days):  # d indexes day number (1-based), comparing M[d-1] and M[d]
        if M[d] != M[d - 1]:  # flight on day d (since M_{d} != M_{d-1} implies F_{d-1} = 1)
            # Close current segment at previous day number d (overlap included)
            segments.append({"day_range": f"Day {current_start}-{d}", "place": current_city})
            current_city = M[d]
            current_start = d  # overlap: start new at day d

    # Close last segment to Day 12
    segments.append({"day_range": f"Day {current_start}-{total_days}", "place": current_city})

    print(json.dumps({"itinerary": segments}, ensure_ascii=False))

if __name__ == "__main__":
    main()
import json
from constraint import Problem

def main():
    # Configuration and input variables
    total_days = 17
    days = list(range(1, total_days + 1))
    cities = ["Warsaw", "Riga", "Budapest", "Paris"]
    direct_flights = {
        ("Warsaw", "Budapest"),
        ("Warsaw", "Riga"),
        ("Budapest", "Paris"),
        ("Warsaw", "Paris"),
        ("Paris", "Riga"),
    }

    target_days = {
        "Warsaw": 2,
        "Riga": 7,
        "Budapest": 7,
        "Paris": 4,
    }

    # Initialize problem
    problem = Problem()

    # Variables for morning (M_d) and evening (E_d) city for each day, and travel indicator (T_d)
    for d in days:
        problem.addVariable(f"M_{d}", cities)
        problem.addVariable(f"E_{d}", cities)
        problem.addVariable(f"T_{d}", [0, 1])

    # Constraint: Travel and direct flight logic per day
    def travel_and_direct(m, e, t):
        if m == e:
            return t == 0
        else:
            return t == 1 and ((m, e) in direct_flights or (e, m) in direct_flights)

    for d in days:
        problem.addConstraint(travel_and_direct, (f"M_{d}", f"E_{d}", f"T_{d}"))

    # Constraint: Continuity - evening city of day d equals morning city of day d+1
    def continuity(e, m_next):
        return e == m_next

    for d in range(1, total_days):
        problem.addConstraint(continuity, (f"E_{d}", f"M_{d+1}"))

    # Attend Warsaw show on days 1 and 2: ensure being in Warsaw on both days
    # We also fix day 1 to start and end in Warsaw to reduce ambiguity and ensure feasibility
    problem.addConstraint(lambda m: m == "Warsaw", ("M_1",))
    problem.addConstraint(lambda e: e == "Warsaw", ("E_1",))
    # Ensure we depart Warsaw on day 2 (travel away from Warsaw)
    problem.addConstraint(lambda e: e != "Warsaw", ("E_2",))
    problem.addConstraint(lambda t: t == 1, ("T_2",))  # ensure day 2 is a travel day

    # No Warsaw after day 2
    for d in range(3, total_days + 1):
        problem.addConstraint(lambda m: m != "Warsaw", (f"M_{d}",))
        problem.addConstraint(lambda e: e != "Warsaw", (f"E_{d}",))

    # Exactly 3 travel days total (to achieve total counted presence of 20 = 17 + 3)
    t_vars = tuple(f"T_{d}" for d in days)
    def travel_sum_constraint(*tvals):
        return sum(tvals) == 3
    problem.addConstraint(travel_sum_constraint, t_vars)

    # City day presence counts: a day counts for a city if that city is the morning or evening city
    me_vars = [f"M_{d}" for d in days] + [f"E_{d}" for d in days]
    def city_counts_constraint(*vals):
        mapping = {var: val for var, val in zip(me_vars, vals)}
        counts = {c: 0 for c in cities}
        for d in days:
            present = {mapping[f"M_{d}"], mapping[f"E_{d}"]}
            for c in present:
                counts[c] += 1
        return all(counts[c] == target_days[c] for c in cities)
    problem.addConstraint(city_counts_constraint, tuple(me_vars))

    # Wedding in Riga between day 11 and 17 inclusive
    w_vars = [f"M_{d}" for d in range(11, total_days + 1)] + [f"E_{d}" for d in range(11, total_days + 1)]
    def riga_wedding_constraint(*vals):
        mapping = {var: val for var, val in zip(w_vars, vals)}
        for d in range(11, total_days + 1):
            if mapping[f"M_{d}"] == "Riga" or mapping[f"E_{d}"] == "Riga":
                return True
        return False
    problem.addConstraint(riga_wedding_constraint, tuple(w_vars))

    solutions = problem.getSolutions()
    if not solutions:
        print(json.dumps({"error": "No feasible itinerary found with given constraints"}))
        return

    sol = solutions[0]

    # Build presence days for each city
    presence_days = {c: [] for c in cities}
    for d in days:
        m = sol[f"M_{d}"]
        e = sol[f"E_{d}"]
        for c in {m, e}:
            presence_days[c].append(d)

    # Build itinerary blocks in visiting order (sorted by first day presence)
    blocks = []
    order = sorted(cities, key=lambda c: min(presence_days[c]))
    for c in order:
        dlist = presence_days[c]
        first_day = min(dlist)
        last_day = max(dlist)
        blocks.append({
            "day_range": f"Day {first_day}-{last_day}",
            "place": c
        })

    result = {"itinerary": blocks}
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()
import json
from constraint import Problem

def main():
    # Parameters
    total_days = 12
    cities = ["Brussels", "Barcelona", "Split"]
    required_days = {
        "Brussels": 2,
        "Barcelona": 7,
        "Split": 5,
    }
    conference_days_in_brussels = [1, 2]

    # Direct flights (undirected)
    direct_pairs = {frozenset(("Brussels", "Barcelona")), frozenset(("Barcelona", "Split"))}

    def is_direct(a, b):
        if a == b:
            return False
        return frozenset((a, b)) in direct_pairs

    days = list(range(1, total_days + 1))
    problem = Problem()

    # Variables:
    # O_d: origin (start-of-day) city on day d
    # T_d: flight destination on day d, or None for no flight
    for d in days:
        problem.addVariable(f"O_{d}", cities)
        problem.addVariable(f"T_{d}", [None] + cities)

    # Constraint: If flying on day d, it must be a direct flight from origin
    for d in days:
        def adjacency_constraint(o, t, _d=d):
            return (t is None) or is_direct(o, t)
        problem.addConstraint(adjacency_constraint, (f"O_{d}", f"T_{d}"))

    # Continuity: The next day's origin equals today's end city (destination if flight, else origin)
    for d in range(1, total_days):
        def continuity(o_today, t_today, o_next, _d=d):
            end_city = t_today if t_today is not None else o_today
            return o_next == end_city
        problem.addConstraint(continuity, (f"O_{d}", f"T_{d}", f"O_{d+1}"))

    # Must be in Brussels on conference days (can be origin or destination due to flying)
    for d in conference_days_in_brussels:
        def brussels_presence(o, t, _d=d):
            return (o == "Brussels") or (t == "Brussels")
        problem.addConstraint(brussels_presence, (f"O_{d}", f"T_{d}"))

    # Optional pruning: On non-conference days, do not be in Brussels (will also be enforced by exact count)
    for d in days:
        if d not in conference_days_in_brussels:
            def not_brussels(o, t, _d=d):
                return not ((o == "Brussels") or (t == "Brussels"))
            problem.addConstraint(not_brussels, (f"O_{d}", f"T_{d}"))

    # Exactly required days per city considering flight-day double counting
    all_O_vars = [f"O_{d}" for d in days]
    all_T_vars = [f"T_{d}" for d in days]

    def city_day_counts(*vals):
        # vals ordered as O_1..O_12, T_1..T_12
        n = total_days
        O_vals = vals[:n]
        T_vals = vals[n:]
        counts = {c: 0 for c in cities}
        for i in range(n):
            o = O_vals[i]
            t = T_vals[i]
            seen = {o}
            if t is not None:
                seen.add(t)
            for c in seen:
                counts[c] += 1
        return all(counts[c] == required_days[c] for c in cities)

    problem.addConstraint(city_day_counts, all_O_vars + all_T_vars)

    # Exactly two flight days (since 2+7+5 - 12 = 2)
    def exactly_two_flights(*ts):
        return sum(1 for x in ts if x is not None) == 2
    problem.addConstraint(exactly_two_flights, all_T_vars)

    solution = problem.getSolution()
    if solution is None:
        print(json.dumps({"itinerary": []}))
        return

    # Build presence per day
    presence = {d: set() for d in days}
    for d in days:
        o = solution[f"O_{d}"]
        t = solution[f"T_{d}"]
        presence[d].add(o)
        if t is not None:
            presence[d].add(t)

    # Build contiguous ranges for each city
    ranges = []
    for city in cities:
        days_here = sorted(d for d in days if city in presence[d])
        if not days_here:
            continue
        start = prev = days_here[0]
        for d in days_here[1:]:
            if d == prev + 1:
                prev = d
            else:
                ranges.append((start, prev, city))
                start = prev = d
        ranges.append((start, prev, city))

    # Sort ranges by start day
    ranges.sort(key=lambda x: x[0])

    itinerary = []
    for s, e, city in ranges:
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
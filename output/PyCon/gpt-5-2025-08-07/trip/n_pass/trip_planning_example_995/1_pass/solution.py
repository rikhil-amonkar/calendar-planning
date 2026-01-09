import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables (trip constraints)
    total_days = 16
    cities = [
        "Oslo", "Brussels", "Split", "Copenhagen", "Barcelona", "Venice", "Stuttgart"
    ]
    durations = {
        "Oslo": 2,
        "Brussels": 3,
        "Split": 4,
        "Copenhagen": 3,
        "Barcelona": 3,
        "Venice": 4,
        "Stuttgart": 3,
    }
    # Direct flights (undirected)
    direct_pairs = [
        ("Venice", "Stuttgart"),
        ("Oslo", "Brussels"),
        ("Split", "Copenhagen"),
        ("Barcelona", "Copenhagen"),
        ("Barcelona", "Venice"),
        ("Brussels", "Venice"),
        ("Barcelona", "Stuttgart"),
        ("Copenhagen", "Brussels"),
        ("Oslo", "Split"),
        ("Oslo", "Venice"),
        ("Barcelona", "Split"),
        ("Oslo", "Copenhagen"),
        ("Barcelona", "Oslo"),
        ("Copenhagen", "Stuttgart"),
        ("Split", "Stuttgart"),
        ("Copenhagen", "Venice"),
        ("Barcelona", "Brussels"),
    ]
    edges = set(frozenset(pair) for pair in direct_pairs)

    # Special constraints
    barcelona_show_days = (1, 3)  # must be in Barcelona days 1-3
    oslo_meet_days = (3, 4)       # must be in Oslo days 3 and 4
    brussels_meet_window = (9, 11)  # must be in Brussels at least one day in 9..11

    # Build CSP
    problem = Problem()

    # Variables: order positions and start days
    order_vars = [f"s{i}" for i in range(1, 8)]
    start_vars = [f"t{i}" for i in range(1, 8)]

    # Domains
    for v in order_vars:
        problem.addVariable(v, cities)
    for t in start_vars:
        problem.addVariable(t, range(1, total_days + 1))

    # All cities appear exactly once
    problem.addConstraint(AllDifferentConstraint(), order_vars)

    # Must start in Barcelona to attend show days 1-3
    problem.addConstraint(lambda s1: s1 == "Barcelona", ["s1"])

    # Must be in Oslo on days 3 and 4 -> Oslo must start on day 3 (with 2-day stay)
    # This is naturally enforced by putting Oslo second after Barcelona (3-day stay)
    problem.addConstraint(lambda s2: s2 == "Oslo", ["s2"])

    # Timeline recursion: t1 = 1
    problem.addConstraint(lambda t1: t1 == 1, ["t1"])

    # t_{k+1} = t_k + duration(s_k) - 1
    for k in range(1, 7):
        sk = f"s{k}"
        tk = f"t{k}"
        tk1 = f"t{k+1}"
        def step_constraint(s_curr, t_curr, t_next, d=durations):
            return t_next == t_curr + d[s_curr] - 1
        problem.addConstraint(step_constraint, (sk, tk, tk1))

    # Ensure final end day is exactly total_days
    def end_day_constraint(s_last, t_last, d=durations, T=total_days):
        return t_last + d[s_last] - 1 == T
    problem.addConstraint(end_day_constraint, ("s7", "t7"))

    # Direct flights between consecutive cities
    for k in range(1, 7):
        sk = f"s{k}"
        sk1 = f"s{k+1}"
        def direct_constraint(a, b, E=edges):
            return frozenset((a, b)) in E
        problem.addConstraint(direct_constraint, (sk, sk1))

    # Must be in Barcelona on days 1-3; with s1=Barcelona and t1=1 and duration 3 that's satisfied.
    # Enforce explicitly that if a position is Barcelona, its start is 1
    for k in range(1, 8):
        sk = f"s{k}"
        tk = f"t{k}"
        def barcelona_timing(city, start, show=barcelona_show_days, d=durations):
            if city != "Barcelona":
                return True
            return start == 1 and d["Barcelona"] == (show[1] - show[0] + 1)
        problem.addConstraint(barcelona_timing, (sk, tk))

    # Oslo meet between day 3 and 4 -> Oslo must start at 3 (2-day stay)
    for k in range(1, 8):
        sk = f"s{k}"
        tk = f"t{k}"
        def oslo_timing(city, start, meet=oslo_meet_days, d=durations):
            if city != "Oslo":
                return True
            return start == meet[0] and d["Oslo"] == (meet[1] - meet[0] + 1)
        problem.addConstraint(oslo_timing, (sk, tk))

    # Brussels must include at least one of days 9..11 -> start in {7,8,9,10,11}
    allowed_brussels_starts = set(range(brussels_meet_window[0] - 2, brussels_meet_window[1] + 1))
    for k in range(1, 8):
        sk = f"s{k}"
        tk = f"t{k}"
        def brussels_timing(city, start, allowed=allowed_brussels_starts):
            if city != "Brussels":
                return True
            return start in allowed
        problem.addConstraint(brussels_timing, (sk, tk))

    # Solve
    solutions = problem.getSolutions()

    if not solutions:
        print(json.dumps({"error": "No feasible itinerary found with given constraints."}))
        return

    # Choose the first solution (any feasible solution satisfies constraints)
    sol = solutions[0]

    # Build itinerary as ordered segments with day ranges
    itinerary = []
    for i in range(1, 8):
        city = sol[f"s{i}"]
        start = sol[f"t{i}"]
        end = start + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    # Output JSON
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
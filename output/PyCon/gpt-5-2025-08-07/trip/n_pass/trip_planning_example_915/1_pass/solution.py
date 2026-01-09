import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and durations (inclusive day counts)
    cities = ["Bucharest", "Venice", "Prague", "Frankfurt", "Zurich", "Florence", "Tallinn"]
    durations = {
        "Bucharest": 3,
        "Venice": 5,
        "Prague": 4,
        "Frankfurt": 5,
        "Zurich": 5,
        "Florence": 5,
        "Tallinn": 5,
    }

    # Direct flight edges (treated as undirected for adjacency purposes)
    def add_edge(a, b, edges_set):
        edges_set.add((a, b))
        edges_set.add((b, a))

    edges = set()
    add_edge("Prague", "Tallinn", edges)
    add_edge("Prague", "Zurich", edges)
    add_edge("Florence", "Prague", edges)
    add_edge("Frankfurt", "Bucharest", edges)
    add_edge("Frankfurt", "Venice", edges)
    add_edge("Prague", "Bucharest", edges)
    add_edge("Bucharest", "Zurich", edges)
    add_edge("Tallinn", "Frankfurt", edges)
    add_edge("Zurich", "Florence", edges)  # "from Zurich to Florence" treated as undirected for simplicity
    add_edge("Frankfurt", "Zurich", edges)
    add_edge("Zurich", "Venice", edges)
    add_edge("Florence", "Frankfurt", edges)
    add_edge("Prague", "Frankfurt", edges)
    add_edge("Tallinn", "Zurich", edges)

    # Problem setup
    n = 7
    problem = Problem()

    # Position variables: P0..P6 (cities)
    pos_vars = [f"P{i}" for i in range(n)]
    for pv in pos_vars:
        problem.addVariable(pv, cities)
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Start day variables: S0..S6 (1..26)
    start_vars = [f"S{i}" for i in range(n)]
    for sv in start_vars:
        problem.addVariable(sv, range(1, 27))

    # Start on Day 1
    problem.addConstraint(lambda s0: s0 == 1, ("S0",))

    # Consecutive segment linkage: next start equals current end (overlap travel day)
    for i in range(n - 1):
        problem.addConstraint(
            lambda city, s_cur, s_next, d=durations: s_next == s_cur + d[city] - 1,
            (f"P{i}", f"S{i}", f"S{i+1}")
        )

    # Direct flight adjacency between consecutive cities
    for i in range(n - 1):
        problem.addConstraint(
            lambda c1, c2, E=edges: (c1, c2) in E,
            (f"P{i}", f"P{i+1}")
        )

    # End exactly on Day 26
    problem.addConstraint(
        lambda city, s_last, d=durations: s_last + d[city] - 1 == 26,
        (f"P{n-1}", f"S{n-1}")
    )

    # Window constraints:
    # - Tallinn must cover Day 8-12 inclusive (5 days => start==8)
    # - Frankfurt must cover Day 12-16 inclusive (5 days => start==12)
    # - Venice must cover Day 22-26 inclusive (5 days => start==22)
    window_requirements = {
        "Tallinn": 8,
        "Frankfurt": 12,
        "Venice": 22,
    }
    for i in range(n):
        for city_name, start_day in window_requirements.items():
            problem.addConstraint(
                lambda c, s, cn=city_name, sd=start_day: (s == sd) if c == cn else True,
                (f"P{i}", f"S{i}")
            )

    # Solve
    sols = problem.getSolutions()
    if not sols:
        print(json.dumps({"itinerary": []}))
        return

    # Pick the first solution deterministically by sorting solutions by start days tuple
    def solution_key(sol):
        return tuple(sol[f"S{i}"] for i in range(n))

    sol = sorted(sols, key=solution_key)[0]

    # Build itinerary in order
    itinerary = []
    for i in range(n):
        city = sol[f"P{i}"]
        s = sol[f"S{i}"]
        e = s + durations[city] - 1
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
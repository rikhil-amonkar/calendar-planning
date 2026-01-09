import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Trip parameters
    total_days = 25
    cities = {
        "Oslo": 2,
        "Helsinki": 2,
        "Edinburgh": 3,
        "Riga": 2,
        "Tallinn": 5,
        "Budapest": 5,
        "Vilnius": 5,
        "Porto": 5,
        "Geneva": 4,
    }
    city_list = list(cities.keys())
    n_cities = len(city_list)
    assert n_cities == 9, "Expected 9 cities."

    # Build directed flight set from the given statements
    directed_edges = set()
    def add_undirected(a, b):
        directed_edges.add((a, b))
        directed_edges.add((b, a))
    def add_directed(a, b):
        directed_edges.add((a, b))

    # Add edges as specified
    add_undirected("Porto", "Oslo")
    add_undirected("Edinburgh", "Budapest")
    add_undirected("Edinburgh", "Geneva")
    add_directed("Riga", "Tallinn")
    add_undirected("Edinburgh", "Porto")
    add_undirected("Vilnius", "Helsinki")
    add_directed("Tallinn", "Vilnius")
    add_undirected("Riga", "Oslo")
    add_undirected("Geneva", "Oslo")
    add_undirected("Edinburgh", "Oslo")
    add_undirected("Edinburgh", "Helsinki")
    add_undirected("Vilnius", "Oslo")
    add_undirected("Riga", "Helsinki")
    add_undirected("Budapest", "Geneva")
    add_undirected("Helsinki", "Budapest")
    add_undirected("Helsinki", "Oslo")
    add_undirected("Edinburgh", "Riga")
    add_undirected("Tallinn", "Helsinki")
    add_undirected("Geneva", "Porto")
    add_undirected("Budapest", "Oslo")
    add_undirected("Helsinki", "Geneva")
    add_directed("Riga", "Vilnius")
    add_undirected("Tallinn", "Oslo")

    # Constraint problem
    problem = Problem()

    # Variables: city positions, start days, end days
    pos_vars = [f"P{i}" for i in range(1, n_cities + 1)]
    start_vars = [f"S{i}" for i in range(1, n_cities + 1)]
    end_vars = [f"E{i}" for i in range(1, n_cities + 1)]

    # Domains
    for p in pos_vars:
        problem.addVariable(p, city_list)
    for s in start_vars:
        problem.addVariable(s, range(1, total_days + 1))
    for e in end_vars:
        problem.addVariable(e, range(1, total_days + 1))

    # All cities visited exactly once
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Start on day 1
    problem.addConstraint(lambda s1: s1 == 1, [start_vars[0]])

    # Link durations: Ei = Si + duration(city) - 1
    def duration_constraint(city, s, e):
        if city is None or s is None or e is None:
            return True
        return e == s + cities[city] - 1

    for i in range(n_cities):
        problem.addConstraint(duration_constraint, [pos_vars[i], start_vars[i], end_vars[i]])

    # Overlap/travel rule: S(i+1) = E(i) so travel day counts for both cities
    for i in range(n_cities - 1):
        problem.addConstraint(lambda e_i, s_next: (e_i is None or s_next is None) or (s_next == e_i),
                              [end_vars[i], start_vars[i + 1]])

    # End on total_days
    problem.addConstraint(lambda e_last: e_last == total_days, [end_vars[-1]])

    # Direct flight constraint between consecutive cities (directed)
    def direct_flight(a, b):
        if a is None or b is None:
            return True
        return (a, b) in directed_edges

    for i in range(n_cities - 1):
        problem.addConstraint(direct_flight, [pos_vars[i], pos_vars[i + 1]])

    # Tallinn wedding between day 4 and 8 (inclusive): segment intersects [4,8]
    def tallinn_wedding(city, s, e):
        if city is None or s is None or e is None:
            return True
        if city != "Tallinn":
            return True
        return (s <= 8) and (e >= 4)

    for i in range(n_cities):
        problem.addConstraint(tallinn_wedding, [pos_vars[i], start_vars[i], end_vars[i]])

    # Oslo meetup between day 24 and 25 (inclusive): segment intersects {24,25}
    def oslo_meetup(city, s, e):
        if city is None or s is None or e is None:
            return True
        if city != "Oslo":
            return True
        return (s <= 24 <= e) or (s <= 25 <= e)

    for i in range(n_cities):
        problem.addConstraint(oslo_meetup, [pos_vars[i], start_vars[i], end_vars[i]])

    # Helpful deterministic preference: place Oslo last ensures meeting on days 24-25 exactly
    problem.addConstraint(lambda c: c == "Oslo", [pos_vars[-1]])

    # Solve
    solutions = problem.getSolutions()

    if not solutions:
        output = {"itinerary": []}
        print(json.dumps(output))
        return

    # Choose a deterministic solution: sort by tuple (P1..P9) then (S1..S9)
    def sol_key(sol):
        return tuple(sol[p] for p in pos_vars) + tuple(sol[s] for s in start_vars)

    solutions.sort(key=sol_key)
    sol = solutions[0]

    # Build itinerary
    itinerary = []
    for i in range(n_cities):
        s = sol[start_vars[i]]
        e = sol[end_vars[i]]
        city = sol[pos_vars[i]]
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
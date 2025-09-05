import json
from z3 import *

def main():
    # Define cities and indices
    cities = ["Dublin", "Krakow", "Istanbul", "Venice", "Naples", "Brussels", "Mykonos", "Frankfurt"]
    idx = {c: i for i, c in enumerate(cities)}

    # Durations (days spent in each city; travel day counts toward both cities due to overlap modeling)
    durations = {
        "Dublin": 5,
        "Krakow": 4,
        "Istanbul": 3,
        "Venice": 3,
        "Naples": 4,
        "Brussels": 2,
        "Mykonos": 4,
        "Frankfurt": 3,
    }

    # Allowed direct flights: treat "X and Y" as bidirectional; "from A to B" as A->B only
    allowed_pairs = set()
    def add_bidirectional(a, b):
        allowed_pairs.add((idx[a], idx[b]))
        allowed_pairs.add((idx[b], idx[a]))
    def add_directed(a, b):
        allowed_pairs.add((idx[a], idx[b]))

    add_bidirectional("Dublin", "Brussels")
    add_bidirectional("Mykonos", "Naples")
    add_bidirectional("Venice", "Istanbul")
    add_bidirectional("Frankfurt", "Krakow")
    add_bidirectional("Naples", "Dublin")
    add_bidirectional("Krakow", "Brussels")
    add_bidirectional("Naples", "Istanbul")
    add_bidirectional("Naples", "Brussels")
    add_bidirectional("Istanbul", "Frankfurt")
    add_directed("Brussels", "Frankfurt")  # directed as stated
    add_bidirectional("Istanbul", "Krakow")
    add_bidirectional("Istanbul", "Brussels")
    add_bidirectional("Venice", "Frankfurt")
    add_bidirectional("Naples", "Frankfurt")
    add_bidirectional("Dublin", "Krakow")
    add_bidirectional("Venice", "Brussels")
    add_bidirectional("Naples", "Venice")
    add_bidirectional("Istanbul", "Dublin")
    add_bidirectional("Venice", "Dublin")
    add_bidirectional("Dublin", "Frankfurt")

    # SMT variables
    n_segments = 8  # exactly 8 cities
    city_vars = [Int(f"city_{i}") for i in range(n_segments)]
    s_vars = [Int(f"s_{i}") for i in range(n_segments)]
    e_vars = [Int(f"e_{i}") for i in range(n_segments)]

    solver = Solver()

    # Domains
    for i in range(n_segments):
        solver.add(And(city_vars[i] >= 0, city_vars[i] < len(cities)))
        solver.add(And(s_vars[i] >= 1, s_vars[i] <= 21))
        solver.add(And(e_vars[i] >= 1, e_vars[i] <= 21))

    # Each city exactly once (permutation of 0..7)
    solver.add(Distinct(city_vars))

    # Trip starts day 1, and chain overlaps: s_{i+1} = e_i (travel on that day counts for both)
    solver.add(s_vars[0] == 1)
    for i in range(n_segments - 1):
        solver.add(s_vars[i + 1] == e_vars[i])

    # Final day ends on day 21
    solver.add(e_vars[-1] == 21)

    # Duration constraints: e_i = s_i + duration(city_i) - 1
    for i in range(n_segments):
        dur_expr = Sum([If(city_vars[i] == idx[c], durations[c], 0) for c in cities])
        solver.add(e_vars[i] == s_vars[i] + dur_expr - 1)

    # Direct flight constraints between consecutive cities
    for i in range(n_segments - 1):
        solver.add(Or([And(city_vars[i] == a, city_vars[i + 1] == b) for (a, b) in allowed_pairs]))

    # Time window constraints:
    # Dublin: exactly days 11-15 (show attendance)
    for i in range(n_segments):
        solver.add(Implies(city_vars[i] == idx["Dublin"], And(s_vars[i] == 11, e_vars[i] == 15)))

    # Istanbul: meet friend between day 9 and 11 (overlap required)
    for i in range(n_segments):
        solver.add(Implies(city_vars[i] == idx["Istanbul"], And(s_vars[i] <= 11, e_vars[i] >= 9)))

    # Mykonos: visit relatives between day 1 and day 4 (overlap required)
    for i in range(n_segments):
        solver.add(Implies(city_vars[i] == idx["Mykonos"], And(s_vars[i] <= 4, e_vars[i] >= 1)))

    # Krakow: 4 days already enforced by duration mapping

    # Venice: 3 days already enforced by duration mapping

    # Naples: 4 days already enforced by duration mapping

    # Brussels: 2 days already enforced by duration mapping

    # Frankfurt: meet friends between day 15 and day 17 (overlap required)
    for i in range(n_segments):
        solver.add(Implies(city_vars[i] == idx["Frankfurt"], And(s_vars[i] <= 15, e_vars[i] >= 17)))

    # Solve
    if solver.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found under given constraints."}))
        return

    m = solver.model()

    # Extract solution
    itinerary = []
    for i in range(n_segments):
        c_idx = m[city_vars[i]].as_long()
        s = m[s_vars[i]].as_long()
        e = m[e_vars[i]].as_long()
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": cities[c_idx]
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
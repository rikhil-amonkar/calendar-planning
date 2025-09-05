import json
from z3 import *

def main():
    # Problem parameters
    days_total = 18
    cities = ["Barcelona", "Frankfurt", "Florence", "Stockholm", "Venice", "Stuttgart", "Salzburg"]
    idx = {c: i for i, c in enumerate(cities)}

    # Required durations (number of days present, counting flight-day overlap)
    required = {
        "Salzburg": 4,
        "Stockholm": 2,
        "Venice": 5,
        "Frankfurt": 4,
        "Florence": 4,
        "Barcelona": 2,
        "Stuttgart": 3,
    }

    # Direct flights (undirected)
    direct_pairs = [
        ("Barcelona", "Frankfurt"),
        ("Florence", "Frankfurt"),
        ("Stockholm", "Barcelona"),
        ("Barcelona", "Florence"),
        ("Venice", "Barcelona"),
        ("Stuttgart", "Barcelona"),
        ("Frankfurt", "Salzburg"),
        ("Stockholm", "Frankfurt"),
        ("Stuttgart", "Stockholm"),
        ("Stuttgart", "Frankfurt"),
        ("Venice", "Stuttgart"),
        ("Venice", "Frankfurt"),
    ]
    # Build allowed set of ordered pairs (i, j)
    allowed = set()
    for a, b in direct_pairs:
        allowed.add((idx[a], idx[b]))
        allowed.add((idx[b], idx[a]))

    # SMT variables
    D = days_total
    n = len(cities)
    c = [Int(f"c_{d}") for d in range(D)]        # primary city (origin of flight if any) on day d
    s = [Int(f"s_{d}") for d in range(D)]        # secondary city (destination if flight)
    t = [Bool(f"t_{d}") for d in range(D)]       # travel on day d?

    solver = Solver()

    # Domain constraints
    for d in range(D):
        solver.add(c[d] >= 0, c[d] < n)
        solver.add(s[d] >= 0, s[d] < n)
        solver.add(Implies(t[d], s[d] != c[d]))
        solver.add(Implies(Not(t[d]), s[d] == c[d]))

    # Continuity: next day's primary city equals today's destination if travelled, else stay
    for d in range(D - 1):
        solver.add(c[d + 1] == If(t[d], s[d], c[d]))

    # Flights must be along direct edges
    def allowed_edge(p, q):
        # Or over all allowed edges
        disj = []
        for (i, j) in allowed:
            disj.append(And(p == i, q == j))
        return Or(disj) if disj else False

    for d in range(D):
        solver.add(Implies(t[d], allowed_edge(c[d], s[d])))

    # Venice show days: must be present in Venice on days 1..5 (indices 0..4)
    VEN = idx["Venice"]
    for d in range(5):
        solver.add(Or(c[d] == VEN, And(t[d], s[d] == VEN)))

    # Exactly 6 travel days (since sum(required)-days_total = 24-18 = 6)
    solver.add(Sum([If(t[d], 1, 0) for d in range(D)]) == 6)

    # Required durations per city
    for city_name, req in required.items():
        i = idx[city_name]
        presence = []
        for d in range(D):
            presence.append(If(c[d] == i, 1, 0))
            presence.append(If(t[d], If(s[d] == i, 1, 0), 0))
        solver.add(Sum(presence) == req)

    # Solve
    if solver.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found under given constraints."}))
        return

    model = solver.model()

    # Extract model values
    c_vals = [model.evaluate(c[d]).as_long() for d in range(D)]
    s_vals = [model.evaluate(s[d]).as_long() for d in range(D)]
    t_vals = [is_true(model.evaluate(t[d])) for d in range(D)]

    # Build human-readable day descriptions (set of cities present each day)
    day_places = []
    for d in range(D):
        if t_vals[d]:
            place_str = f"{cities[c_vals[d]]} & {cities[s_vals[d]]}"
        else:
            place_str = f"{cities[c_vals[d]]}"
        day_places.append(place_str)

    # Aggregate consecutive days with same place string
    itinerary = []
    start = 0
    current = day_places[0]
    for d in range(1, D):
        if day_places[d] != current:
            itinerary.append({
                "day_range": f"Day {start+1}-{d}",
                "place": current
            })
            start = d
            current = day_places[d]
    # last segment
    itinerary.append({
        "day_range": f"Day {start+1}-{D}",
        "place": current
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
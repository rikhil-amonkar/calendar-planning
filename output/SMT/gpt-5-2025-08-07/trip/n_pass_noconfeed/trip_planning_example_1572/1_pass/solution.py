import json
from z3 import *

def main():
    # Cities and indices
    cities = ["Lyon", "Paris", "Riga", "Berlin", "Stockholm", "Zurich", "Nice", "Seville", "Milan", "Naples"]
    city_index = {c: i for i, c in enumerate(cities)}

    # Durations per city (in days)
    durations = {
        "Lyon": 3,
        "Paris": 5,
        "Riga": 2,
        "Berlin": 2,
        "Stockholm": 3,
        "Zurich": 5,
        "Nice": 2,
        "Seville": 3,
        "Milan": 3,
        "Naples": 4,
    }

    total_days = 23
    num_cities = len(cities)  # 10

    # Direct flights (undirected)
    flight_pairs = [
        ("Paris", "Stockholm"),
        ("Seville", "Paris"),
        ("Naples", "Zurich"),
        ("Nice", "Riga"),
        ("Berlin", "Milan"),
        ("Paris", "Zurich"),
        ("Paris", "Nice"),
        ("Milan", "Paris"),
        ("Milan", "Riga"),
        ("Paris", "Lyon"),
        ("Milan", "Naples"),
        ("Paris", "Riga"),
        ("Berlin", "Stockholm"),
        ("Stockholm", "Riga"),
        ("Nice", "Zurich"),
        ("Milan", "Zurich"),
        ("Lyon", "Nice"),
        ("Zurich", "Stockholm"),
        ("Zurich", "Riga"),
        ("Berlin", "Naples"),
        ("Milan", "Stockholm"),
        ("Berlin", "Zurich"),
        ("Milan", "Seville"),
        ("Paris", "Naples"),
        ("Berlin", "Riga"),
        ("Nice", "Stockholm"),
        ("Berlin", "Paris"),
        ("Nice", "Naples"),
        ("Berlin", "Nice"),
    ]

    # Build directed adjacency set
    edges = set()
    for a, b in flight_pairs:
        ai = city_index[a]
        bi = city_index[b]
        edges.add((ai, bi))
        edges.add((bi, ai))

    # Z3 variables
    pos = [Int(f"pos_{i}") for i in range(num_cities)]  # permutation of city indices
    S_day = [Int(f"S_{i}") for i in range(num_cities)]  # start day (inclusive)
    E_day = [Int(f"E_{i}") for i in range(num_cities)]  # end day (inclusive)

    s = Solver()

    # Domains and permutation constraint
    for i in range(num_cities):
        s.add(pos[i] >= 0, pos[i] < num_cities)
    s.add(Distinct(pos))

    # Day bounds
    for i in range(num_cities):
        s.add(S_day[i] >= 1, E_day[i] >= 1, S_day[i] <= E_day[i], E_day[i] <= total_days)

    # Contiguity and shared travel day rule
    s.add(S_day[0] == 1)          # trip starts on day 1
    s.add(E_day[-1] == total_days)  # trip ends on day total_days
    for i in range(num_cities - 1):
        s.add(S_day[i + 1] == E_day[i])  # shared travel day counts for both cities

    # Duration per segment equals city's planned stay
    def duration_expr(pvar):
        # Build piecewise expression for durations[pos[i]]
        expr = IntVal(0)
        for idx in range(num_cities):
            expr = If(pvar == idx, IntVal(durations[cities[idx]]), expr)
        return expr

    for i in range(num_cities):
        s.add(E_day[i] - S_day[i] + 1 == duration_expr(pos[i]))

    # Direct flight between consecutive cities
    for i in range(num_cities - 1):
        allowed = []
        for (a, b) in edges:
            allowed.append(And(pos[i] == a, pos[i + 1] == b))
        s.add(Or(allowed))

    # Event constraints:
    # Wedding in Berlin on day 1 and 2 => must be in Berlin on both days (forces S=1,E=2 given duration=2)
    berlin_idx = city_index["Berlin"]
    for i in range(num_cities):
        s.add(Implies(pos[i] == berlin_idx, And(S_day[i] <= 1, E_day[i] >= 2)))

    # Nice workshop on day 12 and 13 (forces S=12,E=13 given duration=2)
    nice_idx = city_index["Nice"]
    for i in range(num_cities):
        s.add(Implies(pos[i] == nice_idx, And(S_day[i] <= 12, E_day[i] >= 13)))

    # Stockholm show from day 20 to 22 (forces S=20,E=22 given duration=3)
    stockholm_idx = city_index["Stockholm"]
    for i in range(num_cities):
        s.add(Implies(pos[i] == stockholm_idx, And(S_day[i] <= 20, E_day[i] >= 22)))

    # Check satisfiability
    if s.check() != sat:
        print(json.dumps({"itinerary": [], "status": "unsat"}))
        return

    m = s.model()

    # Extract itinerary
    itinerary = []
    for i in range(num_cities):
        c_idx = m.evaluate(pos[i]).as_long()
        s_i = m.evaluate(S_day[i]).as_long()
        e_i = m.evaluate(E_day[i]).as_long()
        itinerary.append({
            "day_range": f"Day {s_i}-{e_i}",
            "place": cities[c_idx]
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
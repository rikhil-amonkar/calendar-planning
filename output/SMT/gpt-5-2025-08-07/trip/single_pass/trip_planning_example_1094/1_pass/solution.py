import json
from z3 import *

def solve_itinerary():
    # Days
    N_DAYS = 16
    # We'll add a virtual day N_DAYS+1 to allow flights on day 16 (arrival counted on day 16 via day 17 variable)
    TOTAL_VARS = N_DAYS + 1  # days 1..16 plus day 17 for arrival modeling

    # Cities
    cities = ["Vienna", "Barcelona", "Edinburgh", "Krakow", "Riga", "Hamburg", "Paris", "Stockholm"]
    idx = {name: i for i, name in enumerate(cities)}

    # Required total "credited" days per city (including flight-day overlaps)
    required_days = {
        "Vienna": 4,
        "Barcelona": 2,
        "Edinburgh": 4,
        "Krakow": 3,
        "Riga": 4,
        "Hamburg": 2,
        "Paris": 2,
        "Stockholm": 2
    }

    # Build allowed direct flight edges (directed)
    edges = set()

    def add_bidirectional(a, b):
        edges.add((idx[a], idx[b]))
        edges.add((idx[b], idx[a]))

    def add_directed(a, b):
        edges.add((idx[a], idx[b]))

    # Given direct flights: add pairs
    add_bidirectional("Hamburg", "Stockholm")
    add_bidirectional("Vienna", "Stockholm")
    add_bidirectional("Paris", "Edinburgh")
    add_bidirectional("Riga", "Barcelona")
    add_bidirectional("Paris", "Riga")
    add_bidirectional("Krakow", "Barcelona")
    add_bidirectional("Edinburgh", "Stockholm")
    add_bidirectional("Paris", "Krakow")
    add_bidirectional("Krakow", "Stockholm")
    add_bidirectional("Riga", "Edinburgh")
    add_bidirectional("Barcelona", "Stockholm")
    add_bidirectional("Paris", "Stockholm")
    add_bidirectional("Krakow", "Edinburgh")
    add_bidirectional("Vienna", "Hamburg")
    add_bidirectional("Paris", "Hamburg")
    add_bidirectional("Riga", "Stockholm")
    add_bidirectional("Hamburg", "Barcelona")
    add_bidirectional("Vienna", "Barcelona")
    add_bidirectional("Krakow", "Vienna")
    add_directed("Riga", "Hamburg")  # directional
    add_bidirectional("Barcelona", "Edinburgh")
    add_bidirectional("Paris", "Barcelona")
    add_bidirectional("Hamburg", "Edinburgh")
    add_bidirectional("Paris", "Vienna")
    add_bidirectional("Vienna", "Riga")

    # Z3 variables: city per day (1-based indexing; we use a dummy at index 0)
    day_city = [Int(f"city_{d}") for d in range(TOTAL_VARS + 1)]  # indices 0..17, we'll use 1..17

    s = Solver()

    # Domain constraints
    for d in range(1, TOTAL_VARS + 1):  # days 1..17
        s.add(And(day_city[d] >= 0, day_city[d] < len(cities)))

    # Direct-flight or same-city constraints between consecutive days (1..16 and also 16..17)
    allowed_pairs = []
    for (a, b) in edges:
        allowed_pairs.append((a, b))

    def allowed_edge_expr(a_var, b_var):
        return Or(*[And(a_var == a, b_var == b) for (a, b) in allowed_pairs]) if allowed_pairs else False

    for d in range(1, N_DAYS + 1):
        s.add(Or(day_city[d] == day_city[d + 1], allowed_edge_expr(day_city[d], day_city[d + 1])))

    # Helper: whether a given day contributes to a given city (counts flight-day arrival)
    # credit[d][c] is True iff:
    # - day_city[d] == c OR
    # - (day_city[d] != day_city[d+1]) AND (day_city[d+1] == c)
    # Note: We created day 17 so this is valid for d=1..16 (and also d=16 arrival uses day 17).
    def credit_expr(d, c_id):
        return Or(
            day_city[d] == c_id,
            And(day_city[d] != day_city[d + 1], day_city[d + 1] == c_id)
        )

    # City-day count constraints (exact totals)
    for cname, req in required_days.items():
        c_id = idx[cname]
        total_c = Sum([If(credit_expr(d, c_id), 1, 0) for d in range(1, N_DAYS + 1)])
        s.add(total_c == req)

    # Event/window constraints
    # Hamburg: must attend conference on day 10 and day 11 (both days count for Hamburg)
    s.add(credit_expr(10, idx["Hamburg"]))
    s.add(credit_expr(11, idx["Hamburg"]))

    # Paris: wedding between day 1 and day 2 (at least one of these days counts for Paris)
    paris_wedding = Sum([If(credit_expr(d, idx["Paris"]), 1, 0) for d in [1, 2]])
    s.add(paris_wedding >= 1)

    # Edinburgh: meet friend between day 12 and day 15 (at least one of these days counts for Edinburgh)
    edinburgh_meet = Sum([If(credit_expr(d, idx["Edinburgh"]), 1, 0) for d in range(12, 16)])
    s.add(edinburgh_meet >= 1)

    # Stockholm: visit relatives between day 15 and day 16 (at least one counts for Stockholm)
    stockholm_rel = Sum([If(credit_expr(d, idx["Stockholm"]), 1, 0) for d in [15, 16]])
    s.add(stockholm_rel >= 1)

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found"}, indent=2))
        return

    m = s.model()

    # Build itinerary (day -> city for days 1..16)
    itinerary = []
    for d in range(1, N_DAYS + 1):
        city_id = m[day_city[d]].as_long()
        itinerary.append({"day": d, "city": cities[city_id]})

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    solve_itinerary()
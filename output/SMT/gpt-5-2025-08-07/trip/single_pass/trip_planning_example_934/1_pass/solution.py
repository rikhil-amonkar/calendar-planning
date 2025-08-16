import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = ["Brussels", "Rome", "Dubrovnik", "Geneva", "Budapest", "Riga", "Valencia"]
    idx = {c: i for i, c in enumerate(cities)}
    n_days = 17

    # Required total day-counts per city (including flight-day double counting rules)
    targets = {
        "Brussels": 5,
        "Rome": 2,
        "Dubrovnik": 3,
        "Geneva": 5,
        "Budapest": 2,
        "Riga": 4,
        "Valencia": 2
    }

    # Allowed directed flight edges: "A and B" -> both directions; "from X to Y" -> directed X->Y
    allowed = set()

    def add_undirected(a, b):
        allowed.add((idx[a], idx[b]))
        allowed.add((idx[b], idx[a]))

    def add_directed(a, b):
        allowed.add((idx[a], idx[b]))

    add_undirected("Brussels", "Valencia")
    add_undirected("Rome", "Valencia")
    add_undirected("Brussels", "Geneva")
    add_undirected("Rome", "Geneva")
    add_undirected("Dubrovnik", "Geneva")
    add_undirected("Valencia", "Geneva")
    add_directed("Rome", "Riga")  # directed
    add_undirected("Geneva", "Budapest")
    add_undirected("Riga", "Brussels")
    add_undirected("Rome", "Budapest")
    add_undirected("Rome", "Brussels")
    add_undirected("Brussels", "Budapest")
    add_undirected("Dubrovnik", "Rome")

    # Z3 variables: city per day (1..17). Encode as integers 0..len(cities)-1
    city = [Int(f"city_{d}") for d in range(1, n_days + 1)]

    s = Solver()

    # Domain constraints
    for d in range(n_days):
        s.add(And(city[d] >= 0, city[d] < len(cities)))

    # Flight constraints: if city changes from day d-1 to d, the pair must be in allowed edges.
    # (We interpret a flight happens on day d when city[d-1] != city[d])
    for d in range(1, n_days):
        same = city[d] == city[d - 1]
        transitions = [And(city[d - 1] == a, city[d] == b) for (a, b) in allowed]
        s.add(Or(same, Or(transitions)))

    # Helper: presence of city c on day d (counts flight day both for departure and arrival cities)
    # Present on day d if:
    # - city[d] == c (assigned that day), OR
    # - (d>1 and city[d-1] == c and city[d] != city[d-1]) (departing from c on day d)
    def present(c_idx, d_idx):
        d = d_idx  # 0-based index for our arrays
        is_assigned = city[d] == c_idx
        if d == 0:
            return is_assigned
        departed = And(city[d - 1] == c_idx, city[d] != city[d - 1])
        return Or(is_assigned, departed)

    # Exact day-count per city (with flight-day rule)
    for cname, tgt in targets.items():
        c = idx[cname]
        s.add(Sum([If(present(c, d), 1, 0) for d in range(n_days)]) == tgt)

    # The total transitions equals sum(targets) - total_days
    # Because sum(city-day-counts) = total_days + transitions
    total_required = sum(targets.values())
    transitions_needed = total_required - n_days
    s.add(Sum([If(city[d] != city[d - 1], 1, 0) for d in range(1, n_days)]) == transitions_needed)

    # Meeting/workshop window constraints (presence on at least one day in the window)
    # Brussels workshop between day 7 and day 11 inclusive
    s.add(Sum([If(present(idx["Brussels"], d - 1), 1, 0) for d in range(7, 12)]) >= 1)

    # Riga friends between day 4 and day 7 inclusive
    s.add(Sum([If(present(idx["Riga"], d - 1), 1, 0) for d in range(4, 8)]) >= 1)

    # Budapest friend between day 16 and day 17 inclusive
    s.add(Sum([If(present(idx["Budapest"], d - 1), 1, 0) for d in range(16, 18)]) >= 1)

    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found.")

    m = s.model()
    itinerary = []
    for d in range(n_days):
        c_id = m.eval(city[d]).as_long()
        itinerary.append({"day": d + 1, "city": cities[c_id]})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False))
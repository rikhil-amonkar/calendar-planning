# Solve the itinerary planning problem with Z3 and output a JSON dictionary
# with an 'itinerary' key containing a list of day-place mappings.
# Note: Flight days are counted for both the departure and arrival cities,
# so overlap days will appear twice in the itinerary list.

from z3 import *
import json

def solve_itinerary():
    # Cities and lengths (days in each city)
    cities = ["Valencia", "Riga", "Prague", "Mykonos", "Zurich", "Bucharest", "Nice"]
    idx = {c: i for i, c in enumerate(cities)}
    length = {
        "Valencia": 5,
        "Riga": 5,
        "Prague": 3,
        "Mykonos": 3,
        "Zurich": 5,
        "Bucharest": 5,
        "Nice": 2,
    }

    # Allowed direct flights (undirected -> add both directions)
    undirected_edges = [
        ("Mykonos", "Nice"),
        ("Mykonos", "Zurich"),
        ("Prague", "Bucharest"),
        ("Valencia", "Bucharest"),
        ("Zurich", "Prague"),
        ("Riga", "Nice"),
        ("Zurich", "Riga"),
        ("Zurich", "Bucharest"),
        ("Zurich", "Valencia"),
        ("Bucharest", "Riga"),
        ("Prague", "Riga"),
        ("Prague", "Valencia"),
        ("Zurich", "Nice"),
    ]
    allowed_pairs = set()
    for a, b in undirected_edges:
        allowed_pairs.add((idx[a], idx[b]))
        allowed_pairs.add((idx[b], idx[a]))
    allowed_pairs = list(allowed_pairs)

    # Z3 variables:
    # ord[i] = index of city at position i in the path (0..6)
    ord_vars = [Int(f"ord_{i}") for i in range(7)]
    # s[i] = start day (inclusive) of the city at position i
    s_vars = [Int(f"s_{i}") for i in range(7)]

    sol = Solver()

    # Domains
    for i in range(7):
        sol.add(And(ord_vars[i] >= 0, ord_vars[i] <= 6))
        sol.add(And(s_vars[i] >= 1, s_vars[i] <= 22))

    # All positions must be different cities
    sol.add(Distinct(*ord_vars))

    # Adjacency constraints: every consecutive pair must be a direct flight
    for i in range(6):
        sol.add(Or(*[And(ord_vars[i] == a, ord_vars[i+1] == b) for (a, b) in allowed_pairs]))

    # Helper: piecewise (length-1) based on which city is at ord_vars[k]
    def len_minus_1_at(pos_var):
        return Sum([If(pos_var == idx[c], length[c] - 1, 0) for c in cities])

    # Start of first position is day 1
    sol.add(s_vars[0] == 1)

    # Recurrence for starts with overlap: s[i+1] = s[i] + (len(order[i]) - 1)
    for i in range(6):
        sol.add(s_vars[i+1] == s_vars[i] + len_minus_1_at(ord_vars[i]))

    # Anchors:
    # Mykonos: 3 days and wedding between day 1 and day 3 -> Mykonos must be days 1-3 (start=1)
    for k in range(7):
        sol.add(Implies(ord_vars[k] == idx["Mykonos"], s_vars[k] == 1))

    # Prague: 3 days and visit relatives between day 7 and day 9 -> Prague must be days 7-9 (start=7)
    for k in range(7):
        sol.add(Implies(ord_vars[k] == idx["Prague"], s_vars[k] == 7))

    # The end of the last city must be day 22
    last_len_minus_1 = len_minus_1_at(ord_vars[6])
    sol.add(s_vars[6] + last_len_minus_1 == 22)

    # Solve
    if sol.check() != sat:
        raise RuntimeError("No solution found")

    m = sol.model()

    # Build position -> (city, start, length)
    order = []
    for i in range(7):
        city_idx = m.evaluate(ord_vars[i]).as_long()
        city = cities[city_idx]
        start_day = m.evaluate(s_vars[i]).as_long()
        dur = length[city]
        order.append((city, start_day, dur))

    # Build itinerary list with overlap days duplicated at transitions
    itinerary = []
    for city, s_day, dur in order:
        for d in range(s_day, s_day + dur):
            itinerary.append({"day": int(d), "place": city})

    # Output JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    solve_itinerary()
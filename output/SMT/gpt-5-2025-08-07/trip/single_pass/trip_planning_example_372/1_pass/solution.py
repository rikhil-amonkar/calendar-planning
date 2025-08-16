import json
from z3 import *

def solve_itinerary():
    # Days and cities
    N = 13
    cities = ["Madrid", "Porto", "Seville", "Stuttgart"]
    MADRID, PORTO, SEVILLE, STUTTGART = range(4)

    # Desired total presence days (counting flight days for both cities)
    desired_days = {
        MADRID: 4,
        PORTO: 3,
        SEVILLE: 2,
        STUTTGART: 7,
    }

    # Z3 variables: city at the end of each day (1..13 -> index 0..12)
    city_vars = [Int(f"c_{d+1}") for d in range(N)]

    s = Solver()

    # Domain constraints: cities in 0..3
    for v in city_vars:
        s.add(And(v >= 0, v <= 3))

    # Helper: whether a change (flight) occurs between day i and i+1
    # (0-based index i between 0..N-2)
    change = [Bool(f"chg_{i+1}") for i in range(N - 1)]
    for i in range(N - 1):
        s.add(change[i] == (city_vars[i] != city_vars[i + 1]))

    # Exactly the right number of flight days:
    # Sum(desired_days) - N equals number of flights (each flight day is double-counted once)
    flights_needed = sum(desired_days.values()) - N
    s.add(Sum([If(change[i], 1, 0) for i in range(N - 1)]) == flights_needed)

    # Direct flight connectivity (if there is a change, it must be one of the allowed undirected edges)
    def allowed(a, b):
        return Or(
            And(a == PORTO, b == STUTTGART), And(a == STUTTGART, b == PORTO),
            And(a == SEVILLE, b == PORTO),    And(a == PORTO, b == SEVILLE),
            And(a == MADRID, b == PORTO),     And(a == PORTO, b == MADRID),
            And(a == MADRID, b == SEVILLE),   And(a == SEVILLE, b == MADRID),
        )

    for i in range(N - 1):
        s.add(Implies(change[i], allowed(city_vars[i], city_vars[i + 1])))

    # Presence counting:
    # Total presence days in a city = end-of-day days in that city
    #                              + number of times you depart from that city (change from that city to another next day)
    for c in [MADRID, PORTO, SEVILLE, STUTTGART]:
        end_days = Sum([If(city_vars[i] == c, 1, 0) for i in range(N)])
        departures = Sum([If(And(city_vars[i] == c, city_vars[i + 1] != city_vars[i]), 1, 0) for i in range(N - 1)])
        s.add(end_days + departures == desired_days[c])

    # Presence predicate: present(city c) on day idx (0-based)
    def present(idx, c):
        if idx == 0:
            return city_vars[0] == c
        else:
            return Or(
                city_vars[idx] == c,  # end-of-day in c
                And(city_vars[idx - 1] == c, city_vars[idx] != city_vars[idx - 1])  # departed from c on this day
            )

    # Conference in Stuttgart on day 7 and day 13 (indices 6 and 12)
    s.add(present(6, STUTTGART))
    s.add(present(12, STUTTGART))

    # Visit relatives in Madrid between day 1 and day 4 (indices 0..3), i.e., at least one of these days includes Madrid
    s.add(Or([present(i, MADRID) for i in range(4)]))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No valid itinerary found.")

    m = s.model()
    itinerary = []
    for d in range(N):
        city_idx = m[city_vars[d]].as_long()
        itinerary.append({"day": d + 1, "city": cities[city_idx]})

    # Output as required JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    solve_itinerary()
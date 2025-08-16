# Requires: z3-solver
# You can install with: pip install z3-solver

from z3 import *
import json

def solve_itinerary():
    # Constants
    D = 11  # total days
    # City encoding
    KRAKOW, PARIS, SEVILLE = 0, 1, 2
    city_names = {KRAKOW: "Krakow", PARIS: "Paris", SEVILLE: "Seville"}

    # Variables: city on each day (1..11), encoded as integers 0..2
    cities = [Int(f"c_{d}") for d in range(1, D + 1)]

    s = Solver()

    # Domain constraints
    for c in cities:
        s.add(Or(c == KRAKOW, c == PARIS, c == SEVILLE))

    # Allowed direct flights: Krakow <-> Paris, Paris <-> Seville
    def allowed_edge(a, b):
        return Or(
            And(a == KRAKOW, b == PARIS),
            And(a == PARIS, b == KRAKOW),
            And(a == PARIS, b == SEVILLE),
            And(a == SEVILLE, b == PARIS),
        )

    # If a change occurs between day d and d+1, it must be an allowed direct flight
    for i in range(D - 1):
        s.add(Implies(cities[i] != cities[i + 1], allowed_edge(cities[i], cities[i + 1])))

    # Count flights (number of transitions)
    flight_count = Sum([If(cities[i] != cities[i + 1], 1, 0) for i in range(D - 1)])
    s.add(flight_count == 2)  # As totals sum to 13 while days are 11, exactly 2 flight days

    # Helper: does day d (1-based) count for city C under the "flight day counts for both" rule?
    def day_counts_for_city(d, C):
        idx = d - 1  # convert to 0-based index
        base = (cities[idx] == C)
        # arrival on day d is counted for city C if a flight occurs on day d (i.e., between d and d+1)
        # and we arrive to C on day d+1, while not already in C on day d (to avoid double counting)
        arrival = And(idx < D - 1, cities[idx] != C, cities[idx + 1] == C)
        return Or(base, arrival)

    # Totals required:
    # Seville: 6 days, Paris: 2 days, Krakow: 5 days
    total_krakow = Sum([If(day_counts_for_city(d, KRAKOW), 1, 0) for d in range(1, D + 1)])
    total_paris = Sum([If(day_counts_for_city(d, PARIS), 1, 0) for d in range(1, D + 1)])
    total_seville = Sum([If(day_counts_for_city(d, SEVILLE), 1, 0) for d in range(1, D + 1)])

    s.add(total_krakow == 5)
    s.add(total_paris == 2)
    s.add(total_seville == 6)

    # Workshop in Krakow between day 1 and day 5 (inclusive)
    workshop_days = [day_counts_for_city(d, KRAKOW) for d in range(1, 6)]
    s.add(Or(*workshop_days))

    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found.")
    m = s.model()

    itinerary = []
    for d in range(1, D + 1):
        c_val = m.evaluate(cities[d - 1]).as_long()
        itinerary.append({"day": d, "city": city_names[c_val]})

    # Print the JSON-formatted dictionary
    print(json.dumps({"itinerary": itinerary}, indent=2))


if __name__ == "__main__":
    solve_itinerary()
# Requires: z3-solver
# pip install z3-solver

from z3 import *
import json

def solve_itinerary():
    # Cities and indices
    cities = ["Dubrovnik", "Frankfurt", "Krakow", "Oslo", "Naples"]
    DUB, FRA, KRK, OSL, NAP = range(5)
    city_to_idx = {name: i for i, name in enumerate(cities)}

    # Allowed direct flights (undirected)
    direct_pairs = {
        (DUB, OSL), (OSL, DUB),
        (FRA, KRK), (KRK, FRA),
        (FRA, OSL), (OSL, FRA),
        (DUB, FRA), (FRA, DUB),
        (KRK, OSL), (OSL, KRK),
        (NAP, OSL), (OSL, NAP),
        (NAP, DUB), (DUB, NAP),
        (NAP, FRA), (FRA, NAP),
    }

    days = 18
    s = Solver()

    # Decision variables: place[d] is city index on day d (0-based days 0..17 represent Day 1..18)
    place = [Int(f"place_{d}") for d in range(days)]
    for d in range(days):
        s.add(And(place[d] >= 0, place[d] < 5))

    # Only direct flights when changing cities
    for d in range(1, days):
        same_city = place[d] == place[d - 1]
        allowed_change = Or(*[And(place[d - 1] == a, place[d] == b) for (a, b) in direct_pairs])
        s.add(Or(same_city, allowed_change))

    # Count of total days per city considering flight-day double counting:
    # total[c] = mapped_days[c] + outgoing_transitions[c]
    totals_required = {
        DUB: 5,  # Dubrovnik
        FRA: 4,  # Frankfurt
        KRK: 5,  # Krakow
        OSL: 3,  # Oslo
        NAP: 5,  # Naples
    }

    for c in range(5):
        mapped = Sum([If(place[d] == c, 1, 0) for d in range(days)])
        outgoing = Sum([If(And(place[d - 1] == c, place[d] != place[d - 1]), 1, 0) for d in range(1, days)])
        s.add(mapped + outgoing == totals_required[c])

    # Oslo between day 16 and day 18 inclusive (1-based), i.e., indices 15..17
    for d in [15, 16, 17]:
        s.add(place[d] == OSL)

    # Dubrovnik with friends between day 5 and day 9 inclusive (1-based).
    # To achieve exactly 5 counted days for Dubrovnik within 5..9, map Dubrovnik on days 5..8 (indices 4..7),
    # and depart on day 9 (index 8). Ensure Dubrovnik appears only on indices 4..7.
    for d in range(days):
        if 4 <= d <= 7:
            s.add(place[d] == DUB)
        else:
            s.add(place[d] != DUB)

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found.")

    m = s.model()
    itinerary = [{"day": d + 1, "place": cities[m.evaluate(place[d]).as_long()]} for d in range(days)]

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_itinerary()
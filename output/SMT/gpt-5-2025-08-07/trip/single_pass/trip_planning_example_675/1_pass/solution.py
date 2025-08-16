# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json

def solve_itinerary():
    # Cities and their indices
    cities = ["Dubrovnik", "Split", "Milan", "Porto", "Krakow", "Munich"]
    DUB, SPL, MIL, POR, KRA, MUC = range(6)

    # Allowed direct flights (undirected, but we encode both directions)
    undirected_edges = [
        (MUC, POR),
        (SPL, MIL),
        (MIL, POR),
        (MUC, KRA),
        (MUC, MIL),
        (DUB, MUC),
        (KRA, SPL),
        (KRA, MIL),
        (MUC, SPL),
    ]
    allowed_directed = set()
    for a, b in undirected_edges:
        allowed_directed.add((a, b))
        allowed_directed.add((b, a))

    # Total days
    N = 16

    # Z3 variables: origin[d], dest[d] for day indices 0..N-1 (represent days 1..N)
    origin = [Int(f"origin_{d}") for d in range(N)]
    dest = [Int(f"dest_{d}") for d in range(N)]

    s = Solver()

    # Domain constraints
    for d in range(N):
        s.add(And(origin[d] >= 0, origin[d] < 6))
        s.add(And(dest[d] >= 0, dest[d] < 6))

    # Day-to-day linkage: you end day d in dest[d], you start day d+1 there
    for d in range(N - 1):
        s.add(origin[d + 1] == dest[d])

    # If there's a flight on day d (origin != dest), it must be a direct flight
    for d in range(N):
        s.add(Implies(origin[d] != dest[d],
                      Or([And(origin[d] == a, dest[d] == b) for (a, b) in allowed_directed])))

    # Helper: indicator sum for durations
    def sum_if_equals(arr, city):
        return Sum([If(arr[d] == city, 1, 0) for d in range(N)])

    # Duration counting with flight-day double counting:
    # Each day contributes:
    # - 1 to origin city
    # - +1 to destination city only if a flight happens (origin != dest)
    durations = {}
    for city in range(6):
        start_count = sum_if_equals(origin, city)
        flight_dest_count = Sum([If(And(dest[d] == city, origin[d] != dest[d]), 1, 0) for d in range(N)])
        durations[city] = start_count + flight_dest_count

    # Required days per city
    s.add(durations[DUB] == 4)
    s.add(durations[SPL] == 3)
    s.add(durations[MIL] == 3)
    s.add(durations[POR] == 4)
    s.add(durations[KRA] == 2)
    s.add(durations[MUC] == 5)

    # Number of flights equals (sum of city-days) - total days = 21 - 16 = 5
    flights = Sum([If(origin[d] != dest[d], 1, 0) for d in range(N)])
    s.add(flights == 5)

    # Time window constraints:
    # - Munich: days 4..8 inclusive (indices 3..7) - must be in Munich (origin or dest) each day
    for d in range(3, 8):
        s.add(Or(origin[d] == MUC, dest[d] == MUC))
    # - Krakow: days 8..9 inclusive (indices 7..8)
    for d in range(7, 9):
        s.add(Or(origin[d] == KRA, dest[d] == KRA))
    # - Milan: days 11..13 inclusive (indices 10..12)
    for d in range(10, 13):
        s.add(Or(origin[d] == MIL, dest[d] == MIL))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Build itinerary: per instructions, no separate flight entries; choose the city you start the day in (origin)
    itinerary = []
    for d in range(N):
        day_city_idx = m[origin[d]].as_long()
        itinerary.append({"day": d + 1, "place": cities[day_city_idx]})

    # Output JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    solve_itinerary()
import json
from z3 import *

def solve_itinerary():
    # Define cities and indices
    cities = ["Prague", "Stuttgart", "Split", "Krakow", "Florence"]
    P, S, SP, K, F = [cities.index(n) for n in cities]

    # Days indexed 0..7 (representing Day 1..8)
    num_days = 8
    C = [Int(f"C_{d}") for d in range(num_days)]

    # Domain constraints: C[d] is a valid city index
    s = Solver()
    for d in range(num_days):
        s.add(And(C[d] >= 0, C[d] < len(cities)))

    # Direct flight edges (undirected)
    undirected_edges = [
        (S, SP),   # Stuttgart - Split
        (P, F),    # Prague - Florence
        (K, S),    # Krakow - Stuttgart
        (K, SP),   # Krakow - Split
        (SP, P),   # Split - Prague
        (K, P),    # Krakow - Prague
    ]
    directed_edges = []
    for a, b in undirected_edges:
        directed_edges.append((a, b))
        directed_edges.append((b, a))

    # Connectivity: if city changes from day d-1 to d, the pair must be a direct flight
    for d in range(1, num_days):
        s.add(Or(
            C[d] == C[d-1],
            Or([And(C[d-1] == u, C[d] == v) for (u, v) in directed_edges])
        ))

    # Helper: presence predicate for city on a given day (0-based day index)
    def present(city, day):
        if day == 0:
            return C[0] == city
        return Or(C[day] == city, And(C[day-1] == city, C[day] != city))

    # City-day counts with the "flight day counts for both cities" rule
    def city_total(city):
        stay_days = [If(C[d] == city, 1, 0) for d in range(num_days)]
        # departure days: day d counts for city if previous day was that city and we left it
        dep_days = [If(And(C[d-1] == city, C[d] != city), 1, 0) for d in range(1, num_days)]
        return Sum(stay_days) + Sum(dep_days)

    # Exact stay requirements
    s.add(city_total(P) == 4)   # Prague 4 days
    s.add(city_total(S) == 2)   # Stuttgart 2 days
    s.add(city_total(SP) == 2)  # Split 2 days
    s.add(city_total(K) == 2)   # Krakow 2 days
    s.add(city_total(F) == 2)   # Florence 2 days

    # Special constraints:
    # Wedding in Stuttgart between day 2 and day 3 => present on Day 2 and Day 3
    s.add(present(S, 1))  # Day 2
    s.add(present(S, 2))  # Day 3

    # Meet friends in Split between day 3 and day 4 => present on Day 3 and Day 4
    s.add(present(SP, 2))  # Day 3
    s.add(present(SP, 3))  # Day 4

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    m = s.model()
    itinerary = []
    for d in range(num_days):
        city_idx = m[C[d]].as_long()
        itinerary.append({"day": d + 1, "city": cities[city_idx]})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))
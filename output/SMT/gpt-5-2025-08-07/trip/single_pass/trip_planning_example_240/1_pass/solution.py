# Requires: z3-solver
# pip install z3-solver

from z3 import *
import json

def solve_itinerary():
    days = 12

    # City encoding
    P, B, T, S = 0, 1, 2, 3
    city_names = {P: "Prague", B: "Berlin", T: "Tallinn", S: "Stockholm"}

    # Allowed direct flights (undirected)
    allowed_edges = {
        (B, T), (T, B),
        (P, T), (T, P),
        (S, T), (T, S),
        (P, S), (S, P),
        (S, B), (B, S),
    }

    # Variables: city[0] is Day 1, ..., city[11] is Day 12
    city = [Int(f"city_{d+1}") for d in range(days)]

    s = Solver()

    # Domain constraints
    for d in range(days):
        s.add(Or(city[d] == P, city[d] == B, city[d] == T, city[d] == S))

    # Direct flight constraint: if city changes from day d to d+1, it must be an allowed edge
    for d in range(days - 1):
        s.add(Implies(city[d] != city[d + 1],
                      Or([And(city[d] == a, city[d + 1] == b) for (a, b) in allowed_edges])))

    # Helper: count city-days with flight-day double counting rule
    def count_city(c):
        assigned = Sum([If(city[d] == c, 1, 0) for d in range(days)])
        arrivals = Sum([If(And(city[d] != city[d + 1], city[d + 1] == c), 1, 0) for d in range(days - 1)])
        return assigned + arrivals

    # Length of stay constraints (with double-counting)
    s.add(count_city(P) == 2)  # Prague
    s.add(count_city(B) == 3)  # Berlin
    s.add(count_city(T) == 5)  # Tallinn
    s.add(count_city(S) == 5)  # Stockholm

    # Conference in Berlin on Day 6 and Day 8
    # Being in Berlin on Day X means: City[X] == B OR City[X+1] == B (arrival on X)
    # Indices: Day X -> index X-1
    s.add(Or(city[5] == B, city[6] == B))  # Day 6
    s.add(Or(city[7] == B, city[8] == B))  # Day 8

    # Visit relatives in Tallinn between Day 8 and Day 12 (inclusive)
    # Each day D in [8..12] must count for Tallinn: city[D] == T or (D < 12 and city[D+1] == T)
    for D in range(8, 12):  # D=8..11 -> index D-1 has a next day
        i = D - 1
        s.add(Or(city[i] == T, city[i + 1] == T))
    # Day 12 specifically must be assigned Tallinn (no next day to rely on arrival)
    s.add(city[11] == T)

    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found under given constraints.")

    m = s.model()

    itinerary = []
    for d in range(days):
        itinerary.append({"day": d + 1, "city": city_names[m[city[d]].as_long()]})

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    solve_itinerary()
from z3 import *
import json

def solve_itinerary():
    # City encoding
    cities = {"Madrid": 0, "Dublin": 1, "Tallinn": 2}
    city_names = {v: k for k, v in cities.items()}

    days = 7

    # Variables: loc[d] is the city (0..2) for day d+1
    loc = [Int(f"loc_{d+1}") for d in range(days)]

    s = Solver()

    # Domain constraints
    for d in range(days):
        s.add(And(loc[d] >= 0, loc[d] <= 2))

    # Workshop in Tallinn on Day 6 and Day 7
    s.add(loc[5] == cities["Tallinn"])
    s.add(loc[6] == cities["Tallinn"])

    # Allowed direct flight edges (undirected)
    M = cities["Madrid"]
    D = cities["Dublin"]
    T = cities["Tallinn"]
    allowed_edges = [(M, D), (D, M), (D, T), (T, D)]

    # If we change cities from day i to day i+1, the pair must be directly connected
    for i in range(1, days):
        change = loc[i] != loc[i - 1]
        allowed_change = Or(*[And(loc[i - 1] == a, loc[i] == b) for (a, b) in allowed_edges])
        s.add(Implies(change, allowed_change))

    # Count total days per city including flight-day double counting
    def total_days_for(c):
        # Base count: days where loc[d] == c
        base = Sum([If(loc[d] == c, 1, 0) for d in range(days)])
        # Extra count: for each change day (day i+1), add 1 to the previous city
        extra = Sum([If(And(loc[i] != loc[i - 1], loc[i - 1] == c), 1, 0) for i in range(1, days)])
        return base + extra

    # Required totals
    s.add(total_days_for(M) == 4)
    s.add(total_days_for(D) == 3)
    s.add(total_days_for(T) == 2)

    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found.")

    m = s.model()

    itinerary = []
    for d in range(days):
        city_val = m[loc[d]].as_long()
        itinerary.append({"day": d + 1, "city": city_names[city_val]})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_itinerary()
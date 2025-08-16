from z3 import *
import json

def solve_itinerary():
    # City indices
    M, D, V, S = 0, 1, 2, 3
    city_names = {M: "Manchester", D: "Madrid", V: "Vienna", S: "Stuttgart"}

    days = 15  # Days 1..15, we'll index 0..14 in code

    # Variables: city_on_day[i] is the city you're in at the end of day i+1
    city_on_day = [Int(f"city_{i+1}") for i in range(days)]

    s = Solver()

    # Domain constraints
    for i in range(days):
        s.add(And(city_on_day[i] >= 0, city_on_day[i] <= 3))

    # Allowed direct flights (both directions)
    allowed = set([
        (V, S), (S, V),
        (M, V), (V, M),
        (D, V), (V, D),
        (M, S), (S, M),
        (M, D), (D, M),
    ])

    # If there's a change between consecutive days, it must be along an allowed edge
    for i in range(1, days):
        s.add(Implies(
            city_on_day[i] != city_on_day[i - 1],
            Or(*[And(city_on_day[i - 1] == a, city_on_day[i] == b) for (a, b) in allowed])
        ))

    # Helper: whether a given day counts for city c (double-count flight day for both departure and arrival)
    def counts_for_city(c, i):
        if i == 0:
            # Day 1 counts only for the city you are in on Day 1
            return city_on_day[0] == c
        # Day i counts for c if you're in c at end of day i,
        # or if you departed from c on day i (i.e., previous day was c and you changed city)
        return Or(
            city_on_day[i] == c,
            And(city_on_day[i - 1] == c, city_on_day[i] != city_on_day[i - 1])
        )

    # Duration constraints (with double-counting rule)
    s.add(Sum([If(counts_for_city(M, i), 1, 0) for i in range(days)]) == 7)  # Manchester 7 days
    s.add(Sum([If(counts_for_city(D, i), 1, 0) for i in range(days)]) == 4)  # Madrid 4 days
    s.add(Sum([If(counts_for_city(V, i), 1, 0) for i in range(days)]) == 2)  # Vienna 2 days
    s.add(Sum([If(counts_for_city(S, i), 1, 0) for i in range(days)]) == 5)  # Stuttgart 5 days

    # Workshop in Stuttgart between day 11 and day 15 inclusive: must count for Stuttgart on each of these days
    for i in range(10, 15):  # indices 10..14 correspond to days 11..15
        s.add(counts_for_city(S, i))

    # Wedding in Manchester between day 1 and day 7 inclusive: must count for Manchester on each of these days
    for i in range(0, 7):  # indices 0..6 correspond to days 1..7
        s.add(counts_for_city(M, i))

    # Exactly 3 flights (because total desired city-days = 18 and calendar days = 15, so 3 flight days double-count)
    flights = Sum([If(city_on_day[i] != city_on_day[i - 1], 1, 0) for i in range(1, days)])
    s.add(flights == 3)

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    itinerary = []
    for i in range(days):
        c = m[city_on_day[i]].as_long()
        itinerary.append({"day": i + 1, "city": city_names[c]})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_itinerary()
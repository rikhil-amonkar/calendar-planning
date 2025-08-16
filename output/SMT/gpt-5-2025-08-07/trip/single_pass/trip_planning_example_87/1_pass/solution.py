import json
from z3 import *

def solve_itinerary():
    # Cities encoded as integers
    RIGA, AMSTERDAM, MYKONOS = 0, 1, 2
    city_names = {RIGA: "Riga", AMSTERDAM: "Amsterdam", MYKONOS: "Mykonos"}

    days = 7
    # Variables: city per day (1..7)
    c = [Int(f"day_{d}") for d in range(1, days + 1)]
    s = Solver()

    # Domain constraints
    for d in range(days):
        s.add(Or(c[d] == RIGA, c[d] == AMSTERDAM, c[d] == MYKONOS))

    # Allowed direct flights (both directions)
    direct_edges = {(RIGA, AMSTERDAM), (AMSTERDAM, RIGA),
                    (AMSTERDAM, MYKONOS), (MYKONOS, AMSTERDAM)}

    # Movement constraints: stay or direct flight
    for d in range(days - 1):
        stay = c[d] == c[d + 1]
        direct = Or(*[And(c[d] == u, c[d + 1] == v) for (u, v) in direct_edges])
        s.add(Or(stay, direct))

    # Visit relatives in Riga between day 1 and day 2 (i.e., be in Riga on both days)
    s.add(c[0] == RIGA, c[1] == RIGA)

    # Desired total per-city "days," counting flight day for both departure and arrival cities
    desired = {RIGA: 2, AMSTERDAM: 2, MYKONOS: 5}

    # Counting rule:
    # - Presence days: count day d if c[d] == city
    # - Arrival bonus: for d in 1..6, if c[d] != c[d+1] and c[d+1] == city, then day d counts for city (arrival day)
    def presence_count(city):
        return Sum([If(c[d] == city, 1, 0) for d in range(days)])

    def arrival_count(city):
        return Sum([If(And(c[d] != c[d + 1], c[d + 1] == city), 1, 0) for d in range(days - 1)])

    for city in [RIGA, AMSTERDAM, MYKONOS]:
        s.add(presence_count(city) + arrival_count(city) == desired[city])

    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found with the given constraints.")

    m = s.model()
    itinerary = [{"day": d + 1, "city": city_names[m[c[d]].as_long()]} for d in range(days)]
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False, indent=2))
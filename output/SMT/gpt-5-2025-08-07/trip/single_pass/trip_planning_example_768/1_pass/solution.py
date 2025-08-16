import json
from z3 import *

def solve_itinerary():
    # Cities and indices
    cities = ["London", "Copenhagen", "Tallinn", "Oslo", "Mykonos", "Nice"]
    city_to_idx = {name: i for i, name in enumerate(cities)}
    LONDON = city_to_idx["London"]
    COPENHAGEN = city_to_idx["Copenhagen"]
    TALLINN = city_to_idx["Tallinn"]
    OSLO = city_to_idx["Oslo"]
    MYKONOS = city_to_idx["Mykonos"]
    NICE = city_to_idx["Nice"]

    # Allowed direct flights (undirected)
    edges = {
        (LONDON, COPENHAGEN),
        (COPENHAGEN, TALLINN),
        (TALLINN, OSLO),
        (MYKONOS, LONDON),
        (OSLO, NICE),
        (LONDON, NICE),
        (MYKONOS, NICE),
        (LONDON, OSLO),
        (COPENHAGEN, NICE),
        (COPENHAGEN, OSLO),
    }
    # Create ordered adjacency set (both directions)
    allowed_pairs = set()
    for a, b in edges:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))

    # Z3 variables: City on each of 16 days (1..16) -> indices 0..15
    days = 16
    DayCity = [Int(f"day_{d+1}") for d in range(days)]

    s = Solver()

    # Domain constraints
    for d in range(days):
        s.add(And(DayCity[d] >= 0, DayCity[d] < len(cities)))

    # Transition constraints: either same city (no flight) or a direct flight
    for d in range(1, days):
        ors = []
        # same city
        ors.append(DayCity[d] == DayCity[d - 1])
        # any allowed direct flight pair
        for (a, b) in allowed_pairs:
            ors.append(And(DayCity[d] == a, DayCity[d - 1] == b))
        s.add(Or(*ors))

    # Flights count equals 5 (since total desired days sum to 21 and actual days are 16)
    flights = [If(DayCity[d] != DayCity[d - 1], 1, 0) for d in range(1, days)]
    s.add(Sum(flights) == 5)

    # Helper: presence of city c on day d (0-based index)
    def present_on_day(c, d):
        if d == 0:
            # Day 1: present if assigned city is c
            return DayCity[d] == c
        else:
            # Present if assigned city is c OR day d is a flight day from c
            return Or(DayCity[d] == c, And(DayCity[d - 1] == c, DayCity[d] != DayCity[d - 1]))

    # City total day counts (including flight-day double-count for departure city)
    def city_total_days(c):
        assigned = Sum([If(DayCity[d] == c, 1, 0) for d in range(days)])
        departures = Sum([If(And(DayCity[d - 1] == c, DayCity[d] != DayCity[d - 1]), 1, 0) for d in range(1, days)])
        return assigned + departures

    # Desired durations
    s.add(city_total_days(MYKONOS) == 4)
    s.add(city_total_days(NICE) == 3)
    s.add(city_total_days(LONDON) == 2)
    s.add(city_total_days(COPENHAGEN) == 3)
    s.add(city_total_days(OSLO) == 5)
    s.add(city_total_days(TALLINN) == 4)

    # Presence in Nice on day 14 and day 16 (1-based), i.e., indices 13 and 15
    s.add(present_on_day(NICE, 13))
    s.add(present_on_day(NICE, 15))

    # Meet friend in Oslo between day 10 and day 14 (inclusive): indices 9..13
    s.add(Or(*[present_on_day(OSLO, d) for d in range(9, 14)]))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found.")

    m = s.model()
    itinerary = []
    for d in range(days):
        city_idx = m[DayCity[d]].as_long()
        itinerary.append({"day": d + 1, "place": cities[city_idx]})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False))
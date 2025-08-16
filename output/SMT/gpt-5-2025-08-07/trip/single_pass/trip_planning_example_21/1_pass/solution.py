# Requires: z3-solver
# pip install z3-solver

from z3 import *
import json

def solve_itinerary():
    # Cities
    VENICE, MYKONOS, VIENNA = 0, 1, 2
    city_names = {VENICE: "Venice", MYKONOS: "Mykonos", VIENNA: "Vienna"}

    days = range(1, 11)  # Day 1..10

    # Variables: city_of_day[d] is the city you are in on day d (the "base" city for that day)
    city_of_day = {d: Int(f"city_{d}") for d in days}

    # Flight flags: flight on day d means a flight occurred between day d-1 and day d
    flights = {d: Bool(f"flight_{d}") for d in range(2, 11)}

    s = Solver()

    # Domain constraints
    for d in days:
        s.add(And(city_of_day[d] >= 0, city_of_day[d] <= 2))

    # Flight definitions and direct flight constraints
    def direct(a, b):
        return Or(
            And(a == MYKONOS, b == VIENNA),
            And(a == VIENNA, b == MYKONOS),
            And(a == VIENNA, b == VENICE),
            And(a == VENICE, b == VIENNA),
        )

    for d in range(2, 11):
        s.add(flights[d] == (city_of_day[d] != city_of_day[d - 1]))
        s.add(Or(Not(flights[d]), direct(city_of_day[d - 1], city_of_day[d])))

    # Workshop and Venice stay: must be in Venice on days 5..10 (6 days total)
    for d in range(5, 11):
        s.add(city_of_day[d] == VENICE)

    # Exactly two flight days (since total counts sum to 12 while we have 10 calendar days)
    s.add(Sum([If(flights[d], 1, 0) for d in range(2, 11)]) == 2)

    # Counting rule: each day counts for the day’s city; flight days also count for the previous day's city
    def total_days_in(city_idx):
        base = Sum([If(city_of_day[d] == city_idx, 1, 0) for d in days])
        prev_on_flight = Sum(
            [If(And(flights[d], city_of_day[d - 1] == city_idx), 1, 0) for d in range(2, 11)]
        )
        return base + prev_on_flight

    # Required stays
    s.add(total_days_in(VENICE) == 6)
    s.add(total_days_in(MYKONOS) == 2)
    s.add(total_days_in(VIENNA) == 4)

    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found.")

    m = s.model()

    itinerary = []
    for d in days:
        city_idx = m.evaluate(city_of_day[d]).as_long()
        itinerary.append({"day": d, "city": city_names[city_idx]})

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))


if __name__ == "__main__":
    solve_itinerary()
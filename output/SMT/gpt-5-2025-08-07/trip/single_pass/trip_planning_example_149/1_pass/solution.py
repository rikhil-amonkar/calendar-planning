from z3 import *
import json

def solve_itinerary():
    # Cities encoded as integers
    ISTANBUL, LONDON, SANTORINI = 0, 1, 2
    city_names = {ISTANBUL: "Istanbul", LONDON: "London", SANTORINI: "Santorini"}

    days = range(1, 11)  # Day 1..10

    # Z3 variables: city_end[d] is the end-of-day city on day d
    city_end = {d: Int(f"city_{d}") for d in days}

    s = Solver()

    # Domain constraints
    for d in days:
        s.add(Or(city_end[d] == ISTANBUL, city_end[d] == LONDON, city_end[d] == SANTORINI))

    # Direct flight connectivity constraints for transitions (flights happen on the current day if city changes)
    def direct(prev, curr):
        return Or(
            And(prev == ISTANBUL, curr == LONDON),
            And(prev == LONDON, curr == ISTANBUL),
            And(prev == LONDON, curr == SANTORINI),
            And(prev == SANTORINI, curr == LONDON),
        )

    for d in range(2, 11):
        s.add(Implies(city_end[d] != city_end[d - 1], direct(city_end[d - 1], city_end[d])))

    # Helper: "in city c on day d" (either end-of-day there, or flew out of there on day d)
    def in_city_on_day(c, d):
        if d == 1:
            return city_end[d] == c
        return Or(
            city_end[d] == c,
            And(city_end[d - 1] == c, city_end[d] != city_end[d - 1])
        )

    # Conference constraints: must be in Santorini on day 5 and day 10
    s.add(in_city_on_day(SANTORINI, 5))
    s.add(in_city_on_day(SANTORINI, 10))

    # To keep the output intuitive, ensure end-of-day city is Santorini on day 5 and day 10
    s.add(city_end[5] == SANTORINI)
    s.add(city_end[10] == SANTORINI)

    # Count city-days with the "flight day counts for both origin and destination" rule
    def days_in_city(c):
        count = Sum([If(city_end[d] == c, 1, 0) for d in days])
        # Add origin credit on flight days
        origin_credits = Sum([If(And(city_end[d - 1] == c, city_end[d] != city_end[d - 1]), 1, 0) for d in range(2, 11)])
        return count + origin_credits

    # Desired totals
    s.add(days_in_city(LONDON) == 3)
    s.add(days_in_city(SANTORINI) == 6)
    s.add(days_in_city(ISTANBUL) == 3)

    if s.check() != sat:
        raise RuntimeError("No valid itinerary found under the given constraints.")

    m = s.model()

    itinerary = []
    for d in days:
        itinerary.append({"day": d, "place": city_names[m[city_end[d]].as_long()]})

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    solve_itinerary()
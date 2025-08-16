# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json

def solve_itinerary():
    # Cities encoding
    LONDON, OSLO, SPLIT, PORTO = 0, 1, 2, 3
    city_names = {LONDON: "London", OSLO: "Oslo", SPLIT: "Split", PORTO: "Porto"}

    days = range(1, 17)  # Days 1..16

    # Decision variables: city_of_day[d] = city you end the day in (destination on flight day)
    city_of_day = {d: Int(f"city_{d}") for d in days}

    s = Solver()

    # Domain constraints
    for d in days:
        s.add(Or([city_of_day[d] == c for c in [LONDON, OSLO, SPLIT, PORTO]]))

    # Allowed direct flights (bidirectional)
    allowed_pairs = set([
        (LONDON, OSLO), (OSLO, LONDON),
        (SPLIT, OSLO),  (OSLO, SPLIT),
        (OSLO, PORTO),  (PORTO, OSLO),
        (LONDON, SPLIT),(SPLIT, LONDON),
    ])

    # Movement constraints: if city changes between consecutive days, it must be an allowed direct flight
    for d in range(2, 17):
        s.add(
            Or(
                city_of_day[d] == city_of_day[d - 1],  # no flight
                Or([And(city_of_day[d - 1] == a, city_of_day[d] == b) for (a, b) in allowed_pairs])
            )
        )

    # Presence booleans: present[c][d] is True if you are in city c on day d
    # You are present in today's city; and if today is a flight day, also present in yesterday's city.
    present = {c: {d: Bool(f"present_{c}_{d}") for d in days} for c in [LONDON, OSLO, SPLIT, PORTO]}

    for d in days:
        for c in [LONDON, OSLO, SPLIT, PORTO]:
            if d == 1:
                s.add(present[c][d] == (city_of_day[d] == c))
            else:
                s.add(
                    present[c][d] == Or(
                        city_of_day[d] == c,
                        And(city_of_day[d - 1] == c, city_of_day[d] != city_of_day[d - 1])
                    )
                )

    # Constraints from the problem:
    # - London: 7 days total, and present in London between day 1 and day 7 (inclusive)
    for d in range(1, 8):
        s.add(present[LONDON][d] == True)
    s.add(Sum([If(present[LONDON][d], 1, 0) for d in days]) == 7)

    # - Split: 5 days total, and present in Split from day 7 to day 11 (inclusive)
    for d in range(7, 12):
        s.add(present[SPLIT][d] == True)
    s.add(Sum([If(present[SPLIT][d], 1, 0) for d in days]) == 5)

    # - Oslo: 2 days total
    s.add(Sum([If(present[OSLO][d], 1, 0) for d in days]) == 2)

    # - Porto: 5 days total
    s.add(Sum([If(present[PORTO][d], 1, 0) for d in days]) == 5)

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    m = s.model()

    # Build the itinerary JSON: one entry per day; no separate flight entries
    itinerary = []
    for d in days:
        city = m[city_of_day[d]].as_long()
        itinerary.append({"day": d, "city": city_names[city]})

    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    solve_itinerary()
from z3 import *
import json

def solve_itinerary():
    # Define cities as an enumeration for clarity
    City, (LONDON, SANTORINI, SPLIT) = EnumSort('City', ['London', 'Santorini', 'Split'])
    cities = [LONDON, SANTORINI, SPLIT]
    city_names = {LONDON: 'London', SANTORINI: 'Santorini', SPLIT: 'Split'}

    days = 18
    # Variables: city for each day (1..18), indexed 0..17
    day_city = [Const(f"day_{d+1}", City) for d in range(days)]
    # change[d] is True if there's a flight on day d+1 (i.e., between day d and d+1)
    change = [Bool(f"chg_{d+2}") for d in range(days-1)]  # corresponds to days 2..18

    s = Solver()

    # Domain implicit from EnumSort

    # Conference constraints: Day 12 and Day 18 in Santorini
    s.add(day_city[11] == SANTORINI)
    s.add(day_city[17] == SANTORINI)

    # Define changes and allowed flights (only on changes)
    # Allowed direct flights (undirected): London<->Santorini, Split<->London
    allowed = lambda a, b: Or(And(a == LONDON, b == SANTORINI),
                              And(a == SANTORINI, b == LONDON),
                              And(a == SPLIT, b == LONDON),
                              And(a == LONDON, b == SPLIT))

    for d in range(1, days):
        # change[d-1] is true iff city changes from day d to day d+1
        s.add(change[d-1] == (day_city[d] != day_city[d-1]))
        # If there is a change, it must be an allowed direct flight
        s.add(Implies(change[d-1], allowed(day_city[d-1], day_city[d])))
        # If there is no change, cities must be equal (already enforced by equivalence above)

    # Per-city day counts with flight-day double-counting for origin city
    # Desired totals (counting the flight departure day for both origin and destination)
    desired = {
        LONDON: 7,
        SANTORINI: 7,
        SPLIT: 6
    }

    for c in cities:
        base = Sum([If(day_city[d] == c, 1, 0) for d in range(days)])
        extra = Sum([If(And(change[d], day_city[d-1] == c), 1, 0) for d in range(days-1)])
        s.add(base + extra == desired[c])

    # Solve
    if s.check() != sat:
        # Fallback, though problem should be satisfiable
        print(json.dumps({"itinerary": []}))
        return

    m = s.model()

    # Build JSON itinerary: list of {day, place}
    itinerary = []
    for d in range(days):
        city_val = m[day_city[d]]
        # model may return None for uninterpreted if unconstrained, but they are constrained here
        name = city_names[city_val]
        itinerary.append({"day": d + 1, "place": name})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_itinerary()
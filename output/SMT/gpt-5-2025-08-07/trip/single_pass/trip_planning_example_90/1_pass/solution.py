from z3 import *
import json

def main():
    # Define cities as an EnumSort
    City, (NAPLES, VIENNA, VILNIUS) = EnumSort('City', ['Naples', 'Vienna', 'Vilnius'])

    # Variables
    start = Const('start', City)
    mid = Const('mid', City)
    end = Const('end', City)

    # Flight days (two direct flights)
    F1 = Int('F1')
    F2 = Int('F2')

    s = Solver()

    # Constraints:
    # - Trip length is 17 days, flights occur on days F1 and F2 (1 <= F1 < F2 <= 17)
    s.add(F1 >= 1, F2 >= 1, F1 < F2, F1 <= 17, F2 <= 17)

    # - Only direct flights are allowed: Naples <-> Vienna, Vienna <-> Vilnius
    def is_direct(a, b):
        return Or(And(a == VIENNA, b == NAPLES),
                  And(a == NAPLES, b == VIENNA),
                  And(a == VIENNA, b == VILNIUS),
                  And(a == VILNIUS, b == VIENNA))

    # We will take exactly two flights: start -> mid on day F1, mid -> end on day F2
    s.add(is_direct(start, mid))
    s.add(is_direct(mid, end))

    # It's a simple line graph; ensure all three are distinct (we will also set mid = Vienna)
    s.add(Distinct(start, mid, end))
    s.add(mid == VIENNA)  # Vienna must be the middle city due to direct-flight graph

    # Counting rule with double-count on flight days:
    # - Start city counts days 1..F1 inclusive: count_start = F1
    # - Mid city counts days F1..F2 inclusive: count_mid = (F2 - F1 + 1)
    # - End city counts days F2..17 inclusive: count_end = (18 - F2)
    count_vienna = F2 - F1 + 1
    count_start = F1
    count_end = 18 - F2

    # Map counts to actual cities (Naples, Vienna, Vilnius)
    count_naples = If(start == NAPLES, count_start,
                      If(end == NAPLES, count_end, IntVal(0)))
    count_vilnius = If(start == VILNIUS, count_start,
                       If(end == VILNIUS, count_end, IntVal(0)))

    # Desired stays
    s.add(count_naples == 5)    # Naples: 5 days
    s.add(count_vienna == 7)    # Vienna: 7 days
    s.add(count_vilnius == 7)   # Vilnius: 7 days

    # Must be in Naples on at least one day between day 1 and day 5 (inclusive)
    def naples_on_day(d):
        # A day includes both cities if it's a flight day.
        return Or(
            And(d < F1, start == NAPLES),
            And(d == F1, Or(start == NAPLES, mid == NAPLES)),
            And(And(F1 < d, d < F2), mid == NAPLES),
            And(d == F2, Or(mid == NAPLES, end == NAPLES)),
            And(d > F2, end == NAPLES)
        )

    s.add(Or([naples_on_day(IntVal(d)) for d in range(1, 6)]))

    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    m = s.model()
    f1 = m[F1].as_long()
    f2 = m[F2].as_long()
    c_start = m[start]
    c_mid = m[mid]
    c_end = m[end]

    # Build itinerary mapping one city per day (no separate flight entries).
    # Convention: on flight days, we list the departure city (start on day F1, mid on day F2).
    def city_name(c):
        return str(c)

    itinerary = []
    for d in range(1, 18):
        if d <= f1:
            c = c_start
        elif d <= f2:
            c = c_mid
        else:
            c = c_end
        itinerary.append({"day": d, "place": city_name(c)})

    # Output as JSON-formatted dictionary with 'itinerary' key
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()
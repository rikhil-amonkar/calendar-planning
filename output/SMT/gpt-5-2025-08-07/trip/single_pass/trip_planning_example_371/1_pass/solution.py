import json
from z3 import *

def solve_itinerary():
    # Cities
    VIENNA, STOCKHOLM, NICE, SPLIT = 0, 1, 2, 3
    city_names = {VIENNA: "Vienna", STOCKHOLM: "Stockholm", NICE: "Nice", SPLIT: "Split"}

    # Allowed direct flights (undirected)
    allowed_pairs = {(VIENNA, STOCKHOLM), (VIENNA, NICE), (VIENNA, SPLIT), (STOCKHOLM, SPLIT), (NICE, STOCKHOLM)}
    allowed_oriented = set()
    for a, b in allowed_pairs:
        allowed_oriented.add((a, b))
        allowed_oriented.add((b, a))

    s = Solver()

    # Day assignments (index 0..8 for days 1..9)
    day_city = [Int(f"day_{i+1}") for i in range(9)]
    for d in day_city:
        s.add(Or(d == VIENNA, d == STOCKHOLM, d == NICE, d == SPLIT))

    # Flight indicators for days 1..8 (index 0..7)
    flight = [Bool(f"flight_day_{i+1}") for i in range(8)]
    for i in range(8):
        # flight occurs iff city changes between day i and i+1
        s.add(flight[i] == (day_city[i] != day_city[i+1]))
        # If a flight occurs, it must be on an allowed direct route
        s.add(Implies(
            flight[i],
            Or(*[And(day_city[i] == a, day_city[i+1] == b) for (a, b) in allowed_oriented])
        ))

    # Helper: credited to city c on day i (0-based index)
    def credited_indicator(c, i):
        if i < 8:
            return If(Or(day_city[i] == c, And(day_city[i] != day_city[i+1], day_city[i+1] == c)), 1, 0)
        else:
            # last day has no flight credit from next day
            return If(day_city[i] == c, 1, 0)

    # City day count targets
    target = {
        VIENNA: 2,
        STOCKHOLM: 5,
        NICE: 2,
        SPLIT: 3
    }

    # Enforce exact credited days per city
    for c, t in target.items():
        s.add(Sum([credited_indicator(c, i) for i in range(9)]) == t)

    # Workshop in Vienna on days 1 and 2 (credited to Vienna)
    s.add(credited_indicator(VIENNA, 0) == 1)
    s.add(credited_indicator(VIENNA, 1) == 1)

    # Conference in Split on day 7 and day 9
    s.add(credited_indicator(SPLIT, 6) == 1)  # day 7 credited to Split
    s.add(credited_indicator(SPLIT, 8) == 1)  # day 9 must be Split

    # Optional: exactly 3 flights (sum of city targets 12 = 9 + flights)
    s.add(Sum([If(flight[i], 1, 0) for i in range(8)]) == 3)

    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found under given constraints.")

    m = s.model()
    itinerary = []
    for i in range(9):
        place = city_names[m[day_city[i]].as_long()]
        itinerary.append({"day": i + 1, "place": place})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    solve_itinerary()
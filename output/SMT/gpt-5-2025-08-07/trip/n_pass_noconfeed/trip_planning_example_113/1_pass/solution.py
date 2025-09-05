import json
from z3 import *

def compute_itinerary():
    # Parameters
    days_total = 12
    days = list(range(1, days_total + 1))

    # City encoding
    NAPLES, MILAN, SEVILLE = 0, 1, 2
    city_names = {NAPLES: "Naples", MILAN: "Milan", SEVILLE: "Seville"}

    # Desired day counts per city
    desired_days = {
        NAPLES: 3,
        MILAN: 7,
        SEVILLE: 4
    }

    # Allowed direct flights (unordered pairs as bidirectional)
    allowed_direct = set([(NAPLES, MILAN), (MILAN, NAPLES), (MILAN, SEVILLE), (SEVILLE, MILAN)])

    # Variables: origin[d] is starting city on day d, dest[d] is ending city on day d
    origin = {d: Int(f"origin_{d}") for d in days}
    dest = {d: Int(f"dest_{d}") for d in days}

    s = Solver()

    # Domain constraints
    for d in days:
        s.add(And(origin[d] >= 0, origin[d] <= 2))
        s.add(And(dest[d] >= 0, dest[d] <= 2))

    # Trip continuity: end of day d is start of day d+1
    for d in days[:-1]:
        s.add(dest[d] == origin[d + 1])

    # Direct flights only when changing cities; otherwise stay
    for d in days:
        s.add(Implies(origin[d] == dest[d], True))
        # If flight occurs, it must be an allowed direct route
        s.add(Implies(origin[d] != dest[d],
                      Or(And(origin[d] == NAPLES, dest[d] == MILAN),
                         And(origin[d] == MILAN, dest[d] == NAPLES),
                         And(origin[d] == MILAN, dest[d] == SEVILLE),
                         And(origin[d] == SEVILLE, dest[d] == MILAN))))

    # Helper: whether in city c on day d (counts origin or destination)
    def in_city(c, d):
        return Or(origin[d] == c, dest[d] == c)

    # City day counts
    for c, target in desired_days.items():
        s.add(Sum([If(in_city(c, d), 1, 0) for d in days]) == target)

    # Event attendance: in Seville from day 9 to day 12 (inclusive)
    for d in range(9, 13):
        s.add(in_city(SEVILLE, d))

    # Number of flight days equals overcount relative to total = 14 - 12 = 2
    flights = Sum([If(origin[d] != dest[d], 1, 0) for d in days])
    s.add(flights == 2)

    # Solve
    if s.check() != sat:
        return {"itinerary": []}

    m = s.model()

    # Extract solution
    orig = {d: m[origin[d]].as_long() for d in days}
    dst = {d: m[dest[d]].as_long() for d in days}
    flight_days = [d for d in days if orig[d] != dst[d]]
    flight_days.sort()

    # Build itinerary segments using flight boundaries (overlapping endpoints by rule)
    if len(flight_days) != 2:
        return {"itinerary": []}

    f1, f2 = flight_days
    start_city = orig[1]
    mid_city = dst[f1]
    end_city = dst[f2]

    itinerary = [
        {"day_range": f"Day 1-{f1}", "place": city_names[start_city]},
        {"day_range": f"Day {f1}-{f2}", "place": city_names[mid_city]},
        {"day_range": f"Day {f2}-{days_total}", "place": city_names[end_city]},
    ]

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result))
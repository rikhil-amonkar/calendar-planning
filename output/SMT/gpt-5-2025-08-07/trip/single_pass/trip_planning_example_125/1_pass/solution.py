import json
from z3 import Solver, Int, Sum, If, Or, And

def solve_itinerary():
    # City indices
    STUTTGART, SEVILLE, MANCHESTER = 0, 1, 2
    city_names = {STUTTGART: "Stuttgart", SEVILLE: "Seville", MANCHESTER: "Manchester"}
    total_days = 15

    # Desired presence (including flight-day double counting)
    target_presence = {
        STUTTGART: 6,
        SEVILLE: 7,
        MANCHESTER: 4,
    }

    # Direct flight adjacency (undirected)
    direct_edges = {
        (MANCHESTER, SEVILLE),
        (SEVILLE, MANCHESTER),
        (STUTTGART, MANCHESTER),
        (MANCHESTER, STUTTGART),
    }

    # Z3 variables: city per day (0..14)
    city = [Int(f"city_{d}") for d in range(total_days)]

    s = Solver()

    # Domain constraints
    for d in range(total_days):
        s.add(And(city[d] >= 0, city[d] <= 2))

    # Flight constraints: only direct flights between adjacent days
    # Also count number of flight days (day d is a flight if city[d] != city[d+1])
    flight_bools = []
    for d in range(total_days - 1):
        is_flight = city[d] != city[d + 1]
        flight_bools.append(is_flight)
        # If it's not the same city, it must be a direct flight
        s.add(Or(city[d] == city[d + 1],
                 Or(*[And(city[d] == a, city[d + 1] == b) for (a, b) in direct_edges])))

    # Exactly 2 flights (since 6+7+4 = 17 total presence, 15 days => 2 double-counted days)
    s.add(Sum([If(b, 1, 0) for b in flight_bools]) == 2)

    # Presence counting with the double-counting rule:
    # A person is present in city c on day d if:
    # - city[d] == c (assigned city that day), OR
    # - d is a flight day and city[d+1] == c (arrived; day d counts for both)
    def present_in_city_day(c, d):
        if d < total_days - 1:
            return Or(city[d] == c, And(city[d] != city[d + 1], city[d + 1] == c))
        else:
            # Last day: can only be present if assigned that city (no "next day" to arrive)
            return city[d] == c

    # Enforce target presence counts
    for c, target in target_presence.items():
        s.add(Sum([If(present_in_city_day(c, d), 1, 0) for d in range(total_days)]) == target)

    # Meet friend in Stuttgart between day 1 and day 6 (index 0..5)
    s.add(Or(*[present_in_city_day(STUTTGART, d) for d in range(0, 6)]))

    # Solve
    if s.check() != 1:  # 1 == sat
        raise RuntimeError("No feasible itinerary found.")

    m = s.model()

    itinerary = []
    for d in range(total_days):
        c_idx = m.evaluate(city[d]).as_long()
        itinerary.append({"day": d + 1, "place": city_names[c_idx]})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))
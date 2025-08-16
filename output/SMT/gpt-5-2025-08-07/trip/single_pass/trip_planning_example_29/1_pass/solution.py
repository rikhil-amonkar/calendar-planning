from z3 import *
import json

def solve_itinerary():
    # Cities
    KRAKOW = 0
    DUBROVNIK = 1
    FRANKFURT = 2
    city_names = {KRAKOW: "Krakow", DUBROVNIK: "Dubrovnik", FRANKFURT: "Frankfurt"}

    days = 10

    # Direct flight adjacency (both directions)
    direct_pairs = {
        (FRANKFURT, KRAKOW), (KRAKOW, FRANKFURT),
        (DUBROVNIK, FRANKFURT), (FRANKFURT, DUBROVNIK)
    }

    # Variables: city[day] is the city you end day 'day' in (1-indexed for readability)
    city = [Int(f"city_{d}") for d in range(1, days + 1)]

    s = Solver()

    # Domain constraints
    for d in range(days):
        s.add(Or(city[d] == KRAKOW, city[d] == DUBROVNIK, city[d] == FRANKFURT))

    # Change (flight) indicators for days 2..10
    change = [Bool(f"change_{d}") for d in range(2, days + 1)]
    for d in range(2, days + 1):
        # Flight occurs if city changes from previous day
        s.add(change[d - 2] == (city[d - 1] != city[d - 2]))
        # If flight occurs, it must be along a direct route
        s.add(Implies(change[d - 2],
                      Or(*[And(city[d - 2] == a, city[d - 1] == b) for (a, b) in direct_pairs])))

    # Attendance in Krakow on days 9 and 10 (wedding period)
    s.add(city[8] == KRAKOW)   # Day 9
    s.add(city[9] == KRAKOW)   # Day 10

    # Exactly 2 flights total (since total desired city-days sum to 12 and trip is 10 days)
    s.add(Sum([If(c, 1, 0) for c in change]) == 2)

    # Count days per city with the double-count rule on flight days:
    # Each day counts for city[day].
    # Additionally, on a flight day d (d>=2), the departure city city[d-1] also gets +1 for day d.
    def city_count(target):
        count_regular = Sum([If(city[d] == target, 1, 0) for d in range(days)])
        count_departure = Sum([If(And(change[d - 2], city[d - 2] == target), 1, 0) for d in range(2, days + 1)])
        return count_regular + count_departure

    # Desired durations
    s.add(city_count(KRAKOW) == 2)
    s.add(city_count(DUBROVNIK) == 7)
    s.add(city_count(FRANKFURT) == 3)

    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    m = s.model()
    itinerary = []
    for d in range(1, days + 1):
        c = m[city[d - 1]].as_long()
        itinerary.append({"day": d, "city": city_names[c]})

    print(json.dumps({"itinerary": itinerary}, indent=2))


if __name__ == "__main__":
    solve_itinerary()
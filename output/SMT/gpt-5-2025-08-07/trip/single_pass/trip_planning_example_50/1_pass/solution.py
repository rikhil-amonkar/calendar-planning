from z3 import *
import json

def solve_itinerary():
    # Constants
    cities = ["Vilnius", "Munich", "Mykonos"]
    VILNIUS, MUNICH, MYKONOS = 0, 1, 2
    total_days = 12

    # Required city-day counts (flight days count for both departure and arrival cities)
    required_days = {
        VILNIUS: 4,
        MUNICH: 3,
        MYKONOS: 7
    }

    # Allowed direct flights (directed where specified, and bidirectional where clear)
    # Interpreting problem statement as:
    # - Direct flight between Munich and Mykonos (both directions)
    # - Direct flight from Vilnius to Munich (directional)
    allowed_direct = {
        (VILNIUS, MUNICH),
        (MUNICH, MYKONOS),
        (MYKONOS, MUNICH),
    }

    # Z3 variables: city at the end of each day (1..12)
    c = [Int(f"c_{d}") for d in range(1, total_days + 1)]

    s = Solver()

    # Domain constraints
    for d in range(total_days):
        s.add(And(c[d] >= 0, c[d] < len(cities)))

    # Movement constraints: if we change city on day d, it must be an allowed direct flight
    for d in range(1, total_days):  # comparing day d (index d) with previous day (index d-1)
        s.add(Or(
            c[d] == c[d - 1],  # no flight
            Or(*[
                And(c[d - 1] == fr, c[d] == to)
                for (fr, to) in allowed_direct
            ])
        ))

    # Count flights = number of transitions
    flights = Sum([If(c[d] != c[d - 1], 1, 0) for d in range(1, total_days)])
    # Based on totals 4 + 3 + 7 = 14 and total_days = 12, flights must be 2
    s.add(flights == 2)

    # City-day counting with "flight days count for both departure and arrival"
    for city in [VILNIUS, MUNICH, MYKONOS]:
        # Days counted while being in 'city' at end of day
        end_days = Sum([If(c[d] == city, 1, 0) for d in range(total_days)])
        # Departure counts: a flight day counts also for the city you left
        departures = Sum([
            If(And(c[d] != c[d - 1], c[d - 1] == city), 1, 0)
            for d in range(1, total_days)
        ])
        s.add(end_days + departures == required_days[city])

    if s.check() != sat:
        raise RuntimeError("No feasible itinerary satisfies the constraints.")

    m = s.model()
    itinerary = []
    for d in range(total_days):
        city_idx = m[c[d]].as_long()
        itinerary.append({"day": d + 1, "place": cities[city_idx]})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_itinerary()
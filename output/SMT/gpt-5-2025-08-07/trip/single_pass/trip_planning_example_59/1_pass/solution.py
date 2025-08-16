from z3 import *
import json

def solve_itinerary():
    # Constants
    DAYS = 16
    BUCHAREST, LYON, PORTO = 0, 1, 2
    CITY_NAMES = {BUCHAREST: "Bucharest", LYON: "Lyon", PORTO: "Porto"}

    # Z3 variables
    city = [None] + [Int(f"city_{d}") for d in range(1, DAYS + 1)]  # 1-based indexing
    flight = [None] + [Bool(f"flight_{d}") for d in range(1, DAYS + 1)]

    s = Solver()

    # Domain constraints for city variables
    for d in range(1, DAYS + 1):
        s.add(And(city[d] >= 0, city[d] <= 2))

    # No flight on day 1 (start in one city)
    s.add(flight[1] == False)

    # Movement and flight constraints (direct flights only between allowed pairs)
    for d in range(2, DAYS + 1):
        # A flight occurs iff the city changes
        s.add(flight[d] == (city[d] != city[d - 1]))
        # If there is a flight, it must be along an allowed edge
        s.add(Implies(
            flight[d],
            Or(
                And(city[d - 1] == BUCHAREST, city[d] == LYON),
                And(city[d - 1] == LYON, city[d] == BUCHAREST),
                And(city[d - 1] == LYON, city[d] == PORTO),
                And(city[d - 1] == PORTO, city[d] == LYON),
            )
        ))

    # Total number of flights must be 2 (since total city-days sum to 18 with double-counting)
    s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS + 1)]) == 2)

    # City-day counts with double counting on flight days:
    # Day d counts for destination city city[d] always;
    # if flight[d] (d >= 2), day d also counts for origin city city[d-1].
    def total_days_for_city(c):
        dest_counts = [If(city[d] == c, 1, 0) for d in range(1, DAYS + 1)]
        origin_counts = [If(And(flight[d], city[d - 1] == c), 1, 0) for d in range(2, DAYS + 1)]
        return Sum(dest_counts + origin_counts)

    s.add(total_days_for_city(BUCHAREST) == 7)
    s.add(total_days_for_city(LYON) == 7)
    s.add(total_days_for_city(PORTO) == 4)

    # Wedding in Bucharest between day 1 and day 7 (inclusive):
    # Being in Bucharest on day d is true if city[d] == Bucharest,
    # or if flying out on day d from Bucharest (flight[d] and city[d-1] == Bucharest).
    wedding_days = []
    for d in range(1, 8):
        if d == 1:
            wedding_days.append(city[d] == BUCHAREST)
        else:
            wedding_days.append(Or(city[d] == BUCHAREST, And(flight[d], city[d - 1] == BUCHAREST)))
    s.add(Or(wedding_days))

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": []}, indent=2))
        return

    m = s.model()

    # Build itinerary JSON (no separate flight entries; just day-city mapping)
    itinerary = []
    for d in range(1, DAYS + 1):
        itinerary.append({"day": d, "city": CITY_NAMES[m[city[d]].as_long()]})

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    solve_itinerary()
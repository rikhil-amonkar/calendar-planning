import json
from z3 import Solver, Int, Or, And, If, Sum

def solve_itinerary():
    # Constants
    n_days = 12
    cities = ["Dublin", "Riga", "Vilnius"]
    D, R, V = 0, 1, 2

    # Desired city-day counts (including flight day counted for both origin and destination)
    desired_counts = {
        D: 2,  # Dublin
        R: 5,  # Riga
        V: 7   # Vilnius
    }

    # Allowed direct flights (directed edges)
    # "Dublin and Riga" -> both directions between Dublin and Riga.
    # "from Riga to Vilnius" -> directed edge from Riga to Vilnius.
    allowed_pairs = [
        (D, R), (R, D),  # Dublin <-> Riga
        (R, V)           # Riga -> Vilnius
    ]

    # Z3 variables for each day: which city you're in at the end of the day
    day_city = [Int(f"day_{i+1}") for i in range(n_days)]

    s = Solver()

    # Domain constraints: 0=Dublin, 1=Riga, 2=Vilnius
    for dc in day_city:
        s.add(Or(dc == D, dc == R, dc == V))

    # Transition constraints: if there's a change from day i to i+1, it must be an allowed direct flight
    for i in range(1, n_days):
        prev_city = day_city[i - 1]
        curr_city = day_city[i]
        allowed_change = Or(*[And(prev_city == a, curr_city == b) for (a, b) in allowed_pairs])
        s.add(Or(curr_city == prev_city, allowed_change))

    # Count number of flights (city changes) and enforce exactly 2 flights
    flights = [If(day_city[i] != day_city[i - 1], 1, 0) for i in range(1, n_days)]
    s.add(Sum(flights) == 2)

    # City-day counts including flight day counted for both origin and destination
    for c in [D, R, V]:
        # Days counted for being in city c at end of day
        dest_days = Sum([If(day_city[i] == c, 1, 0) for i in range(n_days)])
        # Plus days where a flight occurred with origin city c (i.e., previous day city == c)
        origin_flight_days = Sum([If(And(day_city[i] != day_city[i - 1], day_city[i - 1] == c), 1, 0)
                                  for i in range(1, n_days)])
        total_c_days = dest_days + origin_flight_days
        s.add(total_c_days == desired_counts[c])

    if s.check() != 1:  # 1 == sat
        raise RuntimeError("No feasible itinerary found under given constraints.")

    m = s.model()
    itinerary = []
    for i in range(n_days):
        city_idx = m[day_city[i]].as_long()
        itinerary.append({"day": i + 1, "place": cities[city_idx]})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False))
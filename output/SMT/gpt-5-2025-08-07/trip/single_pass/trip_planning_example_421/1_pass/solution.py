# Requires: z3-solver
# pip install z3-solver

from z3 import *
import json

def solve_itinerary():
    # Cities and indices
    cities = ["Nice", "Dublin", "Krakow", "Lyon", "Frankfurt"]
    NICE, DUBLIN, KRAKOW, LYON, FRANKFURT = range(5)

    # Allowed direct flight pairs (undirected)
    undirected_edges = [
        (NICE, DUBLIN),
        (DUBLIN, FRANKFURT),
        (DUBLIN, KRAKOW),
        (KRAKOW, FRANKFURT),
        (LYON, FRANKFURT),
        (NICE, FRANKFURT),
        (LYON, DUBLIN),
        (NICE, LYON),
    ]
    # Expand to both directions
    allowed_pairs = []
    for a, b in undirected_edges:
        allowed_pairs.append((a, b))
        allowed_pairs.append((b, a))

    # Trip length
    D = 20
    days = range(1, D + 1)

    # Z3 variables: city_of_day[d] is the city you are in on day d (end-of-day city)
    city_of_day = [None] + [Int(f"city_{d}") for d in days]  # 1-based

    s = Solver()

    # Domain constraints: each day is one of the 5 cities
    for d in days:
        s.add(And(city_of_day[d] >= 0, city_of_day[d] <= 4))

    # Flight change indicator: a change occurs on day d if city d != city d-1
    changes = [None] + [Bool(f"change_{d}") for d in days]
    for d in days:
        if d == 1:
            # No previous day to compare for the first day
            s.add(changes[d] == False)
        else:
            s.add(changes[d] == (city_of_day[d] != city_of_day[d - 1]))

    # Exactly 4 flights total (since total required city-days = 24 and calendar days = 20)
    s.add(Sum([If(changes[d], 1, 0) for d in days]) == 4)

    # Direct flight constraint: whenever a change occurs, it must be along an allowed edge
    def allowed_change(prev_city, next_city):
        return Or([And(prev_city == a, next_city == b) for (a, b) in allowed_pairs])

    for d in range(2, D + 1):
        s.add(Implies(changes[d], allowed_change(city_of_day[d - 1], city_of_day[d])))

    # Define presence: presence[i][d] is True if city i counts for day d
    # presence(i, d) := (city_of_day[d] == i) or (d > 1 and city_of_day[d-1] == i and city_of_day[d] != city_of_day[d-1])
    def presence(i, d):
        if d == 1:
            return city_of_day[d] == i
        return Or(
            city_of_day[d] == i,
            And(city_of_day[d - 1] == i, city_of_day[d] != city_of_day[d - 1])
        )

    # Duration requirements
    required_days = {
        NICE: 5,
        DUBLIN: 7,
        KRAKOW: 6,
        LYON: 4,
        FRANKFURT: 2
    }
    for i in range(5):
        s.add(Sum([If(presence(i, d), 1, 0) for d in days]) == required_days[i])

    # Window constraints:
    # - Nice between day 1 and 5 (inclusive), exactly those 5 days
    for d in days:
        if 1 <= d <= 5:
            s.add(presence(NICE, d))
        else:
            s.add(Not(presence(NICE, d)))

    # - Frankfurt between day 19 and 20 (inclusive), exactly those 2 days
    for d in days:
        if 19 <= d <= 20:
            s.add(presence(FRANKFURT, d))
        else:
            s.add(Not(presence(FRANKFURT, d)))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    m = s.model()

    # Build JSON itinerary: one entry per day with the city you are in on that day
    itinerary = []
    for d in days:
        city_idx = m.evaluate(city_of_day[d]).as_long()
        itinerary.append({"day": d, "place": cities[city_idx]})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))
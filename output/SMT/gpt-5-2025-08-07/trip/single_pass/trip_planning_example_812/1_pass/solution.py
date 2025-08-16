import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = ["Paris", "Florence", "Vienna", "Porto", "Munich", "Nice", "Warsaw"]
    idx = {c: i for i, c in enumerate(cities)}

    # Trip length
    N = 20

    # Required total presence (counted with the flight-day rule)
    required_days = {
        "Paris": 5,
        "Florence": 3,
        "Vienna": 2,
        "Porto": 3,
        "Munich": 5,
        "Nice": 5,
        "Warsaw": 3,
    }

    # Build allowed directed flight pairs
    allowed = set()
    def add_bidir(a, b):
        allowed.add((idx[a], idx[b]))
        allowed.add((idx[b], idx[a]))
    def add_dir(a, b):
        allowed.add((idx[a], idx[b]))

    # Given direct flights
    add_bidir("Florence", "Vienna")
    add_bidir("Paris", "Warsaw")
    add_bidir("Munich", "Vienna")
    add_bidir("Porto", "Vienna")
    add_bidir("Warsaw", "Vienna")
    add_dir("Florence", "Munich")  # directed
    add_bidir("Munich", "Warsaw")
    add_bidir("Munich", "Nice")
    add_bidir("Paris", "Florence")
    add_bidir("Warsaw", "Nice")
    add_bidir("Porto", "Munich")
    add_bidir("Porto", "Nice")
    add_bidir("Paris", "Vienna")
    add_bidir("Nice", "Vienna")
    add_bidir("Porto", "Paris")
    add_bidir("Paris", "Nice")
    add_bidir("Paris", "Munich")
    add_bidir("Porto", "Warsaw")

    # Decision variables: city per day (primary assignment for the day)
    c = [Int(f"c_{t}") for t in range(1, N + 1)]

    s = Solver()

    # Domain constraints
    for t in range(N):
        s.add(And(c[t] >= 0, c[t] < len(cities)))

    # Flight (adjacency) constraints: if changing city between day t and t+1, it must be a direct flight
    for t in range(N - 1):
        same = c[t] == c[t + 1]
        # allowed transitions
        transitions = [And(c[t] == a, c[t + 1] == b) for (a, b) in allowed]
        s.add(Or(same, Or(*transitions)))

    # Presence calculation with flight-day rule:
    # On day t (1..19): present in X if c[t]==X OR c[t+1]==X (flight day t counts for both origin and destination)
    # On day 20: present in X iff c[20]==X
    def presence_day_city(t, city_idx):
        if t < N:
            return Or(c[t - 1] == city_idx, c[t] == city_idx)  # using 0-based indexing for c list
        else:
            return c[N - 1] == city_idx

    # City total presence requirements
    for city_name, req in required_days.items():
        x = idx[city_name]
        total = Sum([If(presence_day_city(t, x), 1, 0) for t in range(1, N + 1)])
        s.add(total == req)

    # Time-window constraints using presence (not just assignment):
    # Porto workshop between day 1 and day 3 (inclusive)
    for t in [1, 2, 3]:
        s.add(presence_day_city(t, idx["Porto"]))

    # Warsaw wedding between day 13 and day 15 (inclusive)
    for t in [13, 14, 15]:
        s.add(presence_day_city(t, idx["Warsaw"]))

    # Vienna relatives between day 19 and day 20 (inclusive)
    for t in [19, 20]:
        s.add(presence_day_city(t, idx["Vienna"]))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found with the given constraints.")

    m = s.model()
    itinerary = []
    for day in range(1, N + 1):
        city_id = m[c[day - 1]].as_long()
        itinerary.append({"day": day, "city": cities[city_id]})

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    solve_itinerary()
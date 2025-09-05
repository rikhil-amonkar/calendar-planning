import json
from z3 import *

def main():
    # Cities
    cities = [
        "Bucharest", "Krakow", "Munich", "Barcelona", "Warsaw",
        "Budapest", "Stockholm", "Riga", "Edinburgh", "Vienna"
    ]
    idx = {c: i for i, c in enumerate(cities)}

    # Required total presence days per city (counted by being at start or end of a day)
    required_days = {
        "Bucharest": 2,
        "Krakow": 4,
        "Munich": 3,
        "Barcelona": 5,
        "Warsaw": 5,
        "Budapest": 5,
        "Stockholm": 2,
        "Riga": 5,
        "Edinburgh": 5,
        "Vienna": 5
    }

    # Event windows: inclusive [start_day, end_day]
    windows = [
        ("Edinburgh", 1, 5),
        ("Budapest", 9, 13),
        ("Stockholm", 17, 18),
        ("Munich", 18, 20),
        ("Warsaw", 25, 29),
    ]

    # Build flight adjacency (direct flights).
    # "A and B" means bidirectional; "from Riga to Munich" means directional (Riga -> Munich) only.
    edges = set()
    def add_and(a, b):
        edges.add((idx[a], idx[b]))
        edges.add((idx[b], idx[a]))
    def add_from(a, b):
        edges.add((idx[a], idx[b]))

    add_and("Budapest", "Munich")
    add_and("Bucharest", "Riga")
    add_and("Munich", "Krakow")
    add_and("Munich", "Warsaw")
    add_and("Munich", "Bucharest")
    add_and("Edinburgh", "Stockholm")
    add_and("Barcelona", "Warsaw")
    add_and("Edinburgh", "Krakow")
    add_and("Barcelona", "Munich")
    add_and("Stockholm", "Krakow")
    add_and("Budapest", "Vienna")
    add_and("Barcelona", "Stockholm")
    add_and("Stockholm", "Munich")
    add_and("Edinburgh", "Budapest")
    add_and("Barcelona", "Riga")
    add_and("Edinburgh", "Barcelona")
    add_and("Vienna", "Riga")
    add_and("Barcelona", "Budapest")
    add_and("Bucharest", "Warsaw")
    add_and("Vienna", "Krakow")
    add_and("Edinburgh", "Munich")
    add_and("Barcelona", "Bucharest")
    add_and("Edinburgh", "Riga")
    add_and("Vienna", "Stockholm")
    add_and("Warsaw", "Krakow")
    add_and("Barcelona", "Krakow")
    add_from("Riga", "Munich")
    add_and("Vienna", "Bucharest")
    add_and("Budapest", "Warsaw")
    add_and("Vienna", "Warsaw")
    add_and("Barcelona", "Vienna")
    add_and("Budapest", "Bucharest")
    add_and("Vienna", "Munich")
    add_and("Riga", "Warsaw")
    add_and("Stockholm", "Riga")
    add_and("Stockholm", "Warsaw")

    days = 32
    City = IntSort()

    # Variables: start city and end city for each day
    start = [Int(f"start_{d}") for d in range(1, days + 1)]
    end_ = [Int(f"end_{d}") for d in range(1, days + 1)]

    opt = Optimize()

    # Domain constraints
    for d in range(days):
        opt.add(And(start[d] >= 0, start[d] < len(cities)))
        opt.add(And(end_[d] >= 0, end_[d] < len(cities)))

    # Chain continuity: end of day d == start of day d+1
    for d in range(days - 1):
        opt.add(end_[d] == start[d + 1])

    # Direct flight or stay constraint per day
    # If start != end, there must be a direct flight from start to end (directional)
    def allowed_flight_constraint(sd, ed):
        # build disjunction covering all allowed directed edges
        allowed = [And(sd == s, ed == e) for (s, e) in edges]
        return Or(sd == ed, Or(allowed))

    for d in range(days):
        opt.add(allowed_flight_constraint(start[d], end_[d]))

    # Event window constraints: must be in that city (start or end) on each day in the window
    for city, a, b in windows:
        cidx = idx[city]
        for d in range(a - 1, b):  # convert to 0-based
            opt.add(Or(start[d] == cidx, end_[d] == cidx))

    # Total presence days per city equals required_days[city]
    for c, req in required_days.items():
        cidx = idx[c]
        count = []
        for d in range(days):
            count.append(If(Or(start[d] == cidx, end_[d] == cidx), 1, 0))
        opt.add(Sum(count) == req)

    # Optional objective: minimize number of travel days (start != end)
    travel_bools = [If(start[d] != end_[d], 1, 0) for d in range(days)]
    opt.minimize(Sum(travel_bools))

    # Solve
    if opt.check() != sat:
        # If unsat (shouldn't happen if constraints are consistent), output empty itinerary
        print(json.dumps({"itinerary": []}))
        return

    m = opt.model()

    # Build human-readable per-day place string
    day_places = []
    for d in range(days):
        s = m[start[d]].as_long()
        e = m[end_[d]].as_long()
        if s == e:
            place = cities[s]
        else:
            place = f"{cities[s]} -> {cities[e]}"
        day_places.append(place)

    # Compress consecutive days with the same place string into ranges
    itinerary = []
    i = 0
    while i < days:
        j = i
        while j + 1 < days and day_places[j + 1] == day_places[i]:
            j += 1
        day_range = f"Day {i + 1}-{j + 1}" if i != j else f"Day {i + 1}"
        itinerary.append({"day_range": day_range, "place": day_places[i]})
        i = j + 1

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
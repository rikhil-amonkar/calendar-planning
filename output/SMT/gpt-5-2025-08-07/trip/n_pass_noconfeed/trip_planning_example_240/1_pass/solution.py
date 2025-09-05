import json
from z3 import *

def main():
    # Parameters
    total_days = 12
    cities = ["Berlin", "Prague", "Tallinn", "Stockholm"]
    city_index = {name: i for i, name in enumerate(cities)}

    # Required stays (counting flight days in both origin and destination)
    required_stays = {
        "Prague": 2,
        "Berlin": 3,
        "Tallinn": 5,
        "Stockholm": 5,
    }

    # Direct flights (bidirectional)
    direct_edges = {
        ("Berlin", "Tallinn"),
        ("Prague", "Tallinn"),
        ("Stockholm", "Tallinn"),
        ("Prague", "Stockholm"),
        ("Stockholm", "Berlin"),
    }
    # Create directed edges for convenience
    directed_edges = set()
    for a, b in direct_edges:
        directed_edges.add((city_index[a], city_index[b]))
        directed_edges.add((city_index[b], city_index[a]))

    # Z3 Variables
    # Start city on day 0
    s0 = Int("s0")

    # Location at end of each day (1..total_days)
    loc = [Int(f"loc_{d}") for d in range(1, total_days + 1)]

    # Whether a flight occurs on each day (1..total_days)
    fly = [Bool(f"fly_{d}") for d in range(1, total_days + 1)]

    # Presence booleans per day and city
    present = [[Bool(f"present_d{d}_c{c}") for c in range(len(cities))] for d in range(1, total_days + 1)]

    opt = Optimize()

    # Domain constraints
    opt.add(And(s0 >= 0, s0 < len(cities)))
    for d in range(total_days):
        opt.add(And(loc[d] >= 0, loc[d] < len(cities)))

    # Transition constraints and presence definition
    for d in range(1, total_days + 1):
        if d == 1:
            # If flight on day 1, s0 -> loc[0] must be a direct edge; else stay s0
            allowed = Or([And(s0 == a, loc[0] == b) for (a, b) in directed_edges])
            opt.add(If(fly[0], allowed, loc[0] == s0))

            # Presence on day 1: in loc[0] and if flight, also in s0
            for c in range(len(cities)):
                opt.add(present[d - 1][c] == Or(loc[0] == c, And(fly[0], s0 == c)))
        else:
            # If flight on day d, loc[d-2] -> loc[d-1] must be a direct edge; else no change
            allowed = Or([And(loc[d - 2] == a, loc[d - 1] == b) for (a, b) in directed_edges])
            opt.add(If(fly[d - 1], allowed, loc[d - 1] == loc[d - 2]))

            # Presence on day d: in loc[d-1] and if flight, also in loc[d-2]
            for c in range(len(cities)):
                opt.add(present[d - 1][c] == Or(loc[d - 1] == c, And(fly[d - 1], loc[d - 2] == c)))

    # Required stay constraints
    for city_name, req_days in required_stays.items():
        cidx = city_index[city_name]
        opt.add(Sum([If(present[d][cidx], 1, 0) for d in range(total_days)]) == req_days)

    # Conference in Berlin on day 6 and day 8
    opt.add(present[6 - 1][city_index["Berlin"]] == True)
    opt.add(present[8 - 1][city_index["Berlin"]] == True)

    # Visit relatives in Tallinn between day 8 and day 12 (inclusive): must be in Tallinn on those days
    for d in range(8, 12 + 1):
        opt.add(present[d - 1][city_index["Tallinn"]] == True)

    # Optimize: minimize number of flight days
    total_flights = Sum([If(fly[d], 1, 0) for d in range(total_days)])
    opt.minimize(total_flights)

    # Solve
    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = opt.model()

    # Extract presence per day
    day_places = []
    for d in range(1, total_days + 1):
        places = []
        for cidx, cname in enumerate(cities):
            if m.eval(present[d - 1][cidx], model_completion=True):
                places.append(cname)
        # Sort places by fixed order to keep stable output
        place_str = ", ".join(places)
        day_places.append(place_str)

    # Compress into day ranges with identical place sets
    itinerary = []
    start = 1
    current = day_places[0]
    for d in range(2, total_days + 1):
        if day_places[d - 1] != current:
            itinerary.append({"day_range": f"Day {start}-{d-1}", "place": current})
            start = d
            current = day_places[d - 1]
    itinerary.append({"day_range": f"Day {start}-{total_days}", "place": current})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
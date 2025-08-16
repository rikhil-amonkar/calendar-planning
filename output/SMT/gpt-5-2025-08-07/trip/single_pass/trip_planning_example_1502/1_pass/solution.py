import json
from z3 import *

def solve_itinerary():
    # Cities (10 total)
    cities = [
        "Santorini",   # 0
        "Valencia",    # 1
        "Madrid",      # 2
        "Seville",     # 3
        "Bucharest",   # 4
        "Vienna",      # 5
        "Riga",        # 6
        "Tallinn",     # 7
        "Krakow",      # 8
        "Frankfurt"    # 9
    ]
    idx = {name:i for i,name in enumerate(cities)}

    # Required total "in-city day" counts (including flight days)
    required_days = {
        "Santorini": 3,
        "Valencia": 4,
        "Madrid": 2,
        "Seville": 2,
        "Bucharest": 3,
        "Vienna": 4,
        "Riga": 4,
        "Tallinn": 5,
        "Krakow": 5,
        "Frankfurt": 4
    }

    # Direct flights (directed for "from Riga to Tallinn", bidirectional for "A and B")
    directed_edges = set()

    def add_bidirectional(a, b):
        directed_edges.add((idx[a], idx[b]))
        directed_edges.add((idx[b], idx[a]))

    # Listed connections
    add_bidirectional("Vienna", "Bucharest")
    add_bidirectional("Santorini", "Madrid")
    add_bidirectional("Seville", "Valencia")
    add_bidirectional("Vienna", "Seville")
    add_bidirectional("Madrid", "Valencia")
    add_bidirectional("Bucharest", "Riga")
    add_bidirectional("Valencia", "Bucharest")
    add_bidirectional("Santorini", "Bucharest")
    add_bidirectional("Vienna", "Valencia")
    add_bidirectional("Vienna", "Madrid")
    add_bidirectional("Valencia", "Krakow")
    add_bidirectional("Valencia", "Frankfurt")
    add_bidirectional("Krakow", "Frankfurt")
    # One-way
    directed_edges.add((idx["Riga"], idx["Tallinn"]))
    # More bidirectional
    add_bidirectional("Vienna", "Krakow")
    add_bidirectional("Vienna", "Frankfurt")
    add_bidirectional("Madrid", "Seville")
    add_bidirectional("Santorini", "Vienna")
    add_bidirectional("Vienna", "Riga")
    add_bidirectional("Frankfurt", "Tallinn")
    add_bidirectional("Frankfurt", "Bucharest")
    add_bidirectional("Madrid", "Bucharest")
    add_bidirectional("Frankfurt", "Riga")
    add_bidirectional("Madrid", "Frankfurt")

    # Days
    n_days = 27
    day_vars = [Int(f"day_{d}") for d in range(1, n_days+1)]

    s = Solver()

    # Domain constraints
    for d in range(n_days):
        s.add(And(day_vars[d] >= 0, day_vars[d] < len(cities)))

    # Movement constraints: if city changes from day d-1 to d, the pair must be a direct flight
    for d in range(1, n_days):
        prev_c = day_vars[d-1]
        cur_c = day_vars[d]
        allowed_change = Or(
            prev_c == cur_c,  # no flight (stay)
            Or([
                And(prev_c == fr, cur_c == to)
                for (fr, to) in directed_edges
            ])
        )
        s.add(allowed_change)

    # Helper: in-city indicator reflecting flight-day (both cities count) rule
    def in_city(day_idx_zero_based, city_idx):
        if day_idx_zero_based == 0:
            # Day 1: only the city assigned for Day 1 counts
            return day_vars[0] == city_idx
        else:
            # Day d (1..26): counts if assigned city is city_idx, or if departing from city_idx on this day
            return Or(
                day_vars[day_idx_zero_based] == city_idx,
                And(day_vars[day_idx_zero_based - 1] == city_idx, day_vars[day_idx_zero_based] != day_vars[day_idx_zero_based - 1])
            )

    # Duration constraints for each city
    for name, need in required_days.items():
        c = idx[name]
        total = Sum([If(in_city(d, c), 1, 0) for d in range(n_days)])
        s.add(total == need)

    # Event constraints (days are 1-based in problem; convert to 0-based)
    # Vienna wedding between day 3 and day 6 (inclusive): must be "in" Vienna on days 3..6
    for d in range(3, 7):
        s.add(in_city(d-1, idx["Vienna"]))

    # Madrid show from day 6 to day 7 (inclusive)
    for d in [6, 7]:
        s.add(in_city(d-1, idx["Madrid"]))

    # Krakow with friends between day 11 and day 15 (inclusive)
    for d in range(11, 16):
        s.add(in_city(d-1, idx["Krakow"]))

    # Riga conference on day 20 and day 23
    for d in [20, 23]:
        s.add(in_city(d-1, idx["Riga"]))

    # Tallinn workshop between day 23 and day 27 (inclusive)
    for d in range(23, 28):
        s.add(in_city(d-1, idx["Tallinn"]))

    if s.check() != sat:
        raise RuntimeError("No valid itinerary found under the given constraints.")

    m = s.model()
    itinerary = []
    for d in range(n_days):
        c_idx = m[day_vars[d]].as_long()
        itinerary.append({"day": d+1, "city": cities[c_idx]})

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    solve_itinerary()
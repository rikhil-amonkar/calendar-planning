import json
from z3 import *

def main():
    # Problem parameters (inputs)
    days_total = 13
    cities = ["Porto", "Seville", "Madrid", "Stuttgart"]
    city_idx = {name: i for i, name in enumerate(cities)}
    # Direct flights (undirected)
    direct_edges = {
        (city_idx["Porto"], city_idx["Stuttgart"]),
        (city_idx["Seville"], city_idx["Porto"]),
        (city_idx["Madrid"], city_idx["Porto"]),
        (city_idx["Madrid"], city_idx["Seville"]),
    }
    # Required presence days per city
    required_days = {
        "Seville": 2,
        "Stuttgart": 7,
        "Porto": 3,
        "Madrid": 4,
    }
    conf_days = [7, 13]  # Must be in Stuttgart on these days (presence counts via rule)
    relatives_madrid_window = (1, 4)  # Need presence in Madrid at least one day in this window

    # Z3 variables
    # stay[d]: city index where you end day d (1-based indexing, we'll ignore index 0)
    stay = [Int(f"stay_{d}") for d in range(days_total + 1)]  # index 0 unused
    # flight[d]: whether you fly on day d (moving from stay[d-1] to stay[d])
    flight = [Bool(f"flight_{d}") for d in range(days_total + 1)]  # index 0 unused

    s = Optimize()

    # Domain constraints
    for d in range(1, days_total + 1):
        s.add(And(stay[d] >= 0, stay[d] < len(cities)))
    # No flight on day 1 (no previous day)
    s.add(flight[1] == False)

    # Transition constraints with direct flights only
    def direct(u, v):
        # undirected check
        return Or(*[
            And(u == a, v == b) for (a, b) in list(direct_edges) + [(b, a) for (a, b) in direct_edges]
        ])

    for d in range(2, days_total + 1):
        s.add(Implies(flight[d], And(stay[d] != stay[d - 1], direct(stay[d - 1], stay[d]))))
        s.add(Implies(Not(flight[d]), stay[d] == stay[d - 1]))

    # Presence per day logic:
    # On day d, present cities are:
    # - stay[d] always
    # - and stay[d-1] as well if flight[d] is True
    def present(d, city_index):
        if d == 1:
            return stay[d] == city_index
        return Or(stay[d] == city_index, And(flight[d], stay[d - 1] == city_index))

    # Required presence day counts per city
    for cname, req in required_days.items():
        ci = city_idx[cname]
        s.add(
            Sum([If(present(d, ci), 1, 0) for d in range(1, days_total + 1)]) == req
        )

    # Conference presence constraints
    for cd in conf_days:
        s.add(present(cd, city_idx["Stuttgart"]))

    # Visit relatives in Madrid at least one day within the window
    win_lo, win_hi = relatives_madrid_window
    s.add(Or([present(d, city_idx["Madrid"]) for d in range(win_lo, win_hi + 1)]))

    # Exactly the total implied number of flights:
    # Sum of city-day presences = days_total + number_of_flights
    total_required_presence = sum(required_days.values())
    min_flights_needed = total_required_presence - days_total  # equals 3 with given data
    s.add(Sum([If(flight[d], 1, 0) for d in range(1, days_total + 1)]) == min_flights_needed)

    # Mild optimization: avoid flights on conference days if possible (will be forced optimally by constraints)
    s.minimize(Sum([If(And(BoolVal(True), flight[d]), 1, 0) for d in conf_days]))

    if s.check() != sat:
        print(json.dumps({"itinerary": []}))
        return
    m = s.model()

    # Build per-day "place" string: if flight, show "Prev & Curr", else "Curr"
    day_places = []
    for d in range(1, days_total + 1):
        curr = m[stay[d]].as_long()
        if d == 1 or not is_true(m[flight[d]]):
            place = cities[curr]
        else:
            prev = m[stay[d - 1]].as_long()
            place = f"{cities[prev]} & {cities[curr]}"
        day_places.append(place)

    # Compress consecutive identical place strings into day ranges
    itinerary = []
    start = 1
    prev_place = day_places[0]
    for d in range(2, days_total + 1):
        if day_places[d - 1] != prev_place:
            if start == d - 1:
                dr = f"Day {start}"
            else:
                dr = f"Day {start}-{d - 1}"
            itinerary.append({"day_range": dr, "place": prev_place})
            start = d
            prev_place = day_places[d - 1]
    # Add last segment
    if start == days_total:
        dr = f"Day {start}"
    else:
        dr = f"Day {start}-{days_total}"
    itinerary.append({"day_range": dr, "place": prev_place})

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
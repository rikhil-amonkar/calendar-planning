import json
from z3 import *

def solve_itinerary():
    # Input variables (constraints)
    days_total = 10
    cities = ["Krakow", "Dubrovnik", "Frankfurt"]
    city_idx = {name: i for i, name in enumerate(cities)}

    # Desired presence days in each city (counts include flight-day overlaps)
    desired_presence = {
        "Krakow": 2,
        "Dubrovnik": 7,
        "Frankfurt": 3,
    }

    # Direct flight connections (undirected)
    direct_pairs = [("Frankfurt", "Krakow"), ("Dubrovnik", "Frankfurt")]
    allowed_edges = set()
    for a, b in direct_pairs:
        allowed_edges.add((city_idx[a], city_idx[b]))
        allowed_edges.add((city_idx[b], city_idx[a]))

    # Wedding constraint: must be in Krakow on days 9 and 10
    wedding_city = "Krakow"
    wedding_days = [9, 10]

    # Z3 variables
    city = [Int(f"city_{d}") for d in range(1, days_total + 1)]
    fly = [Bool(f"fly_{d}") for d in range(1, days_total)]  # fly on day d means moving from city_d to city_{d+1}

    s = Solver()

    # Domain constraints for cities
    for d in range(days_total):
        s.add(Or([city[d] == city_idx[name] for name in cities]))

    # Transition constraints with flights
    for d in range(days_total - 1):
        # If fly on day d+1, then must change city to an adjacent one
        s.add(Implies(
            fly[d],
            Or([And(city[d] == a, city[d + 1] == b) for (a, b) in allowed_edges])
        ))
        # If not flying on day d+1, then stay in same city
        s.add(Implies(
            Not(fly[d]),
            city[d] == city[d + 1]
        ))

    # Presence counting:
    # presence[city_i] = sum_{d=1..days} [city[d]==i] + sum_{d=1..days-1} [fly[d] and city[d+1]==i]
    for name, req_days in desired_presence.items():
        i = city_idx[name]
        base_days = [If(city[d] == i, 1, 0) for d in range(days_total)]
        flight_bonus = [If(And(fly[d], city[d + 1] == i), 1, 0) for d in range(days_total - 1)]
        s.add(Sum(base_days + flight_bonus) == req_days)

    # Number of flights implied by total presence sum: sum(desired) = days_total + number_of_flights
    total_presence_required = sum(desired_presence.values())
    flights_required = total_presence_required - days_total
    s.add(Sum([If(f, 1, 0) for f in fly]) == flights_required)

    # Wedding constraints: must be in wedding_city on specified days
    w_idx = city_idx[wedding_city]
    for d in wedding_days:
        # Presence on day d means either primary city that day OR destination of a flight occurring on day d
        if d < days_total:
            s.add(Or(city[d - 1] == w_idx, And(fly[d - 1], city[d] == w_idx)))
        else:
            # Last day cannot use flight as destination (no fly variable for day 10),
            # so must be primary city
            s.add(city[d - 1] == w_idx)

    # Ensure we visit all three cities (implicit from desired_presence > 0, but assert anyway)
    for name in cities:
        i = city_idx[name]
        base_days = [If(city[d] == i, 1, 0) for d in range(days_total)]
        flight_bonus = [If(And(fly[d], city[d + 1] == i), 1, 0) for d in range(days_total - 1)]
        s.add(Sum(base_days + flight_bonus) >= 1)

    if s.check() != sat:
        return {"itinerary": []}

    m = s.model()

    # Extract model values
    city_vals = [m.evaluate(city[d]).as_long() for d in range(days_total)]
    fly_vals = [is_true(m.evaluate(fly[d])) for d in range(days_total - 1)]

    # Compute per-city presence by day
    presence = {i: [False] * (days_total + 1) for i in range(len(cities))}  # 1-indexed days
    for d in range(1, days_total + 1):
        curr = city_vals[d - 1]
        presence[curr][d] = True
        if d < days_total and fly_vals[d - 1]:
            dest = city_vals[d]  # city on next day
            presence[dest][d] = True

    # Build contiguous day ranges for each city (presence-based, which includes flight-day overlaps)
    ranges = []
    for i, name in enumerate(cities):
        d = 1
        city_ranges = []
        while d <= days_total:
            if presence[i][d]:
                start = d
                while d + 1 <= days_total and presence[i][d + 1]:
                    d += 1
                end = d
                city_ranges.append((start, end, name))
            d += 1
        ranges.extend(city_ranges)

    # Sort ranges by start day
    ranges.sort(key=lambda x: x[0])

    itinerary = []
    for start, end, name in ranges:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": name
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result))
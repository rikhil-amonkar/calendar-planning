import json
from z3 import *

def solve_itinerary():
    # Define cities and mapping
    cities = ["Prague", "Frankfurt", "Lyon", "Helsinki", "Naples"]
    city_index = {name: i for i, name in enumerate(cities)}

    # Trip parameters
    total_days = 12

    # Desired stays per city (days count according to presence with flight day double-count rule)
    desired_days = {
        "Frankfurt": 3,
        "Naples": 4,
        "Helsinki": 4,
        "Lyon": 3,
        "Prague": 2
    }

    # Direct flight graph (undirected)
    direct_pairs = [
        ("Prague", "Lyon"),
        ("Prague", "Frankfurt"),
        ("Frankfurt", "Lyon"),
        ("Helsinki", "Naples"),
        ("Helsinki", "Frankfurt"),
        ("Naples", "Frankfurt"),
        ("Prague", "Helsinki"),
    ]
    # Expand pairs to both directions
    allowed_edges = []
    for a, b in direct_pairs:
        ai, bi = city_index[a], city_index[b]
        allowed_edges.append((ai, bi))
        allowed_edges.append((bi, ai))

    # Z3 variables
    # city_end[d]: city at the end of day d (0-based index for days)
    city_end = [Int(f"city_end_{d+1}") for d in range(total_days)]
    # flights[d]: whether a flight occurs on day d (0-based; day 0 has no prior day so set to False)
    flights = [Bool(f"flight_day_{d+1}") for d in range(total_days)]

    s = Solver()

    # Domain constraints
    for d in range(total_days):
        s.add(And(city_end[d] >= 0, city_end[d] < len(cities)))

    # No flight on day 1 (index 0)
    s.add(flights[0] == False)

    # Flight logic and direct flight requirement for days 2..12 (indices 1..11)
    for d in range(1, total_days):
        # A flight occurs iff city changes
        s.add(flights[d] == (city_end[d] != city_end[d-1]))
        # If flight occurs, it must be a direct connection
        s.add(Implies(
            flights[d],
            Or([And(city_end[d-1] == a, city_end[d] == b) for (a, b) in allowed_edges])
        ))

    # Presence definition helper: presence on day d in city c (1 if present, 0 otherwise)
    def presence_expr(d, c):
        if d == 0:
            return If(city_end[0] == c, 1, 0)
        # present if end-of-day city is c OR if a flight occurs departing from c
        return If(Or(city_end[d] == c, And(flights[d], city_end[d-1] == c)), 1, 0)

    # Duration constraints for each city
    for cname, target in desired_days.items():
        c = city_index[cname]
        total_presence = Sum([presence_expr(d, c) for d in range(total_days)])
        s.add(total_presence == target)

    # Show in Helsinki from day 2 to day 5 (1-based), i.e., indices 1..4
    helsinki = city_index["Helsinki"]
    for d in range(1, 5):
        s.add(Or(city_end[d] == helsinki, And(flights[d], city_end[d-1] == helsinki)))

    # Workshop in Prague between day 1 and day 2:
    # Ensure presence in Prague on day 1 and day 2 (indices 0 and 1)
    prague = city_index["Prague"]
    s.add(city_end[0] == prague)  # Day 1 end in Prague ensures presence day 1
    s.add(Or(city_end[1] == prague, And(flights[1], city_end[0] == prague)))  # Presence on day 2

    # Exactly 4 flight days needed because total desired city-days = 16 and total distinct days = 12
    # sum of flights must be 16 - 12 = 4
    s.add(Sum([If(flights[d], 1, 0) for d in range(total_days)]) == 4)

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found given the constraints."}))
        return

    m = s.model()

    # Extract end-of-day cities
    end_cities = [m.evaluate(city_end[d]).as_long() for d in range(total_days)]

    # Build contiguous segments by end-of-day city
    itinerary = []
    start_day = 1
    current_city = end_cities[0]
    for d in range(1, total_days):
        if end_cities[d] != current_city:
            # close segment
            end_day = d  # since d is 0-based day index, end_day corresponds to d
            if start_day == end_day:
                day_range = f"Day {start_day}"
            else:
                day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": cities[current_city]})
            # start new segment
            start_day = d + 1
            current_city = end_cities[d]
    # Close final segment
    if start_day == total_days:
        day_range = f"Day {start_day}"
    else:
        day_range = f"Day {start_day}-{total_days}"
    itinerary.append({"day_range": day_range, "place": cities[current_city]})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    solve_itinerary()
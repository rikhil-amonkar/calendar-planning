import json
from z3 import *

def solve_itinerary():
    # Input variables / parameters
    cities = ["Madrid", "Dublin", "Tallinn"]
    city_to_idx = {name: i for i, name in enumerate(cities)}
    idx_to_city = {i: name for i, name in enumerate(cities)}

    num_days = 7

    # Required days per city (note: flight days count for both origin and destination)
    required_days = {
        "Madrid": 4,
        "Dublin": 3,
        "Tallinn": 2
    }

    # Direct flight connections (bidirectional)
    direct_pairs = {
        (city_to_idx["Madrid"], city_to_idx["Dublin"]),
        (city_to_idx["Dublin"], city_to_idx["Madrid"]),
        (city_to_idx["Dublin"], city_to_idx["Tallinn"]),
        (city_to_idx["Tallinn"], city_to_idx["Dublin"]),
    }

    # Workshop must be in Tallinn on day 6 or day 7 (inclusive OR)
    workshop_city = city_to_idx["Tallinn"]
    workshop_window_days = [6, 7]

    # Z3 variables
    base = [Int(f"base_{d}") for d in range(1, num_days + 1)]  # main city for each day
    flight = [Bool(f"flight_{d}") for d in range(1, num_days + 1)]  # whether a flight occurs on day d
    dest = [Int(f"dest_{d}") for d in range(1, num_days + 1)]  # destination city if a flight occurs on day d

    # Presence booleans: present[city_index][day] = True if in that city on that day (including flight overlap)
    present = [[Bool(f"present_{c}_{d}") for d in range(1, num_days + 1)] for c in range(len(cities))]

    s = Solver()

    # Domain constraints for base and dest cities
    for d in range(num_days):
        s.add(And(base[d] >= 0, base[d] < len(cities)))
        s.add(And(dest[d] >= 0, dest[d] < len(cities)))

    # Flight semantics and adjacency constraints
    for d in range(num_days):
        # If no flight on day d, destination equals base (no move during that day)
        s.add(If(flight[d],
                 And(dest[d] != base[d],
                     Or(*[And(base[d] == a, dest[d] == b) for (a, b) in direct_pairs])),
                 dest[d] == base[d]))

    # Transition of base city to next day:
    # After a flight on day d, the base city for day d+1 becomes the destination of that flight.
    for d in range(num_days - 1):
        s.add(base[d + 1] == If(flight[d], dest[d], base[d]))

    # Define presence: you're in base city; if flight occurs, you're also in destination that same day
    for d in range(num_days):
        for c in range(len(cities)):
            s.add(present[c][d] == Or(base[d] == c, And(flight[d], dest[d] == c)))

    # Exactly two flights (because total desired city-days sum to 9 while total days are 7, needing 2 overlaps)
    s.add(Sum([If(flight[d], 1, 0) for d in range(num_days)]) == 2)

    # Required presence counts per city
    for city_name, req in required_days.items():
        cidx = city_to_idx[city_name]
        s.add(Sum([If(present[cidx][d], 1, 0) for d in range(num_days)]) == req)

    # Workshop in Tallinn on day 6 or day 7
    s.add(Or(*[present[workshop_city][d - 1] for d in workshop_window_days]))

    # Ensure all three cities are actually visited (redundant due to required_days > 0, but explicit)
    for c in range(len(cities)):
        s.add(Sum([If(present[c][d], 1, 0) for d in range(num_days)]) >= 1)

    if s.check() != sat:
        return {"itinerary": []}

    m = s.model()

    # Extract model values
    base_vals = [m.evaluate(base[d]).as_long() for d in range(num_days)]
    flight_vals = [is_true(m.evaluate(flight[d])) for d in range(num_days)]
    dest_vals = [m.evaluate(dest[d]).as_long() for d in range(num_days)]

    # Build itinerary segments with overlapping day at flight boundaries:
    # For each flight on day d, we end current segment at day d, and start next segment also at day d.
    itinerary = []
    current_city = base_vals[0]
    segment_start = 1  # days are 1-indexed for output

    for d in range(1, num_days + 1):
        if flight_vals[d - 1]:
            # Close current segment at day d
            itinerary.append({
                "day_range": f"Day {segment_start}-{d}",
                "place": idx_to_city[current_city]
            })
            # Start next segment also at day d, with destination city
            current_city = dest_vals[d - 1]
            segment_start = d

    # Close the final segment at Day num_days
    itinerary.append({
        "day_range": f"Day {segment_start}-{num_days}",
        "place": idx_to_city[current_city]
    })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False))
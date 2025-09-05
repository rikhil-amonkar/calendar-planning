import json
from z3 import *

def solve_itinerary():
    # Input variables (constraints)
    total_days = 10
    cities = ["Venice", "Mykonos", "Vienna"]
    durations = {
        "Venice": 6,
        "Mykonos": 2,
        "Vienna": 4
    }
    # Workshop presence in Venice on days 5-10 (inclusive)
    workshop_start = 5
    workshop_end = 10

    # Direct flight connections (undirected)
    direct_flights = {("Mykonos", "Vienna"), ("Vienna", "Venice")}

    # Map cities to integer ids
    city_to_id = {c: i for i, c in enumerate(cities)}
    id_to_city = {i: c for c, i in city_to_id.items()}

    # Precompute allowed directed pairs from direct flights
    allowed_pairs = set()
    for a, b in list(direct_flights):
        allowed_pairs.add((city_to_id[a], city_to_id[b]))
        allowed_pairs.add((city_to_id[b], city_to_id[a]))

    # Z3 variables
    City = IntSort()
    # city_main[d]: city at the end of day d (1-indexed)
    city_main = [Int(f"city_main_{d}") for d in range(1, total_days + 1)]
    # flight[d]: did we take a flight on day d? (note: day 1 has no previous day, so no flight)
    flight = [Bool(f"flight_{d}") for d in range(1, total_days + 1)]

    s = Solver()

    # Domain constraints: each day ends in one of the defined cities
    for d in range(total_days):
        s.add(Or([city_main[d] == city_to_id[c] for c in cities]))

    # No flight on day 1
    s.add(flight[0] == False)

    # Flight equivalence and adjacency constraints for days 2..N
    for d in range(1, total_days):
        prev_city = city_main[d - 1]
        curr_city = city_main[d]
        # flight[d] <-> city changes
        s.add(Implies(flight[d], prev_city != curr_city))
        s.add(Implies(Not(flight[d]), prev_city == curr_city))
        # If flight, must be along an allowed pair
        allowed_or = Or([And(prev_city == a, curr_city == b) for (a, b) in allowed_pairs])
        s.add(Implies(flight[d], allowed_or))

    # Presence variables: present[c][d] = are we present in city c on day d (considering flight counts for both)
    present = {
        c: [Bool(f"present_{c}_{d}") for d in range(1, total_days + 1)]
        for c in city_to_id.values()
    }

    for d in range(total_days):
        curr = city_main[d]
        if d == 0:
            # Day 1: present if current city is c
            for c in city_to_id.values():
                s.add(present[c][d] == (curr == c))
        else:
            prev = city_main[d - 1]
            for c in city_to_id.values():
                s.add(present[c][d] ==
                      Or(curr == c, And(flight[d], prev == c)))

    # Duration constraints per city
    for city_name, required_days in durations.items():
        c_id = city_to_id[city_name]
        s.add(Sum([If(present[c_id][d], 1, 0) for d in range(total_days)]) == required_days)

    # Workshop constraint: must be present in Venice for every day in [5..10]
    ven_id = city_to_id["Venice"]
    for d in range(workshop_start - 1, workshop_end):
        s.add(present[ven_id][d] == True)

    # Flights count: with 3 cities and given durations summing to 12 vs 10 days, exactly 2 flight days are needed
    s.add(Sum([If(flight[d], 1, 0) for d in range(1, total_days)]) == 2)

    # Solve
    if s.check() != sat:
        return {"itinerary": []}

    m = s.model()

    # Extract the main city per day (end-of-day city)
    itinerary_days = [id_to_city[m.evaluate(city_main[d]).as_long()] for d in range(total_days)]

    # Build contiguous day ranges for output
    itinerary = []
    start = 1
    current_city = itinerary_days[0]
    for d in range(2, total_days + 1):
        if itinerary_days[d - 1] != current_city:
            itinerary.append({"day_range": f"Day {start}-{d-1}", "place": current_city})
            start = d
            current_city = itinerary_days[d - 1]
    itinerary.append({"day_range": f"Day {start}-{total_days}", "place": current_city})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result))
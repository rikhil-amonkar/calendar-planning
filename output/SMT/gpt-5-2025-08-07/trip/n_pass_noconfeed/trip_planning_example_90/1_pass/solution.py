import json
from z3 import Solver, Int, Bool, If, And, Or, Implies, Sum, sat

def main():
    # Parameters (input variables)
    days_total = 17
    cities = ["Naples", "Vienna", "Vilnius"]
    stay_requirements = {
        "Naples": 5,
        "Vienna": 7,
        "Vilnius": 7
    }
    direct_flights = {
        ("Naples", "Vienna"),
        ("Vienna", "Naples"),
        ("Vienna", "Vilnius"),
        ("Vilnius", "Vienna"),
    }
    relatives_city = "Naples"
    relatives_window = (1, 5)  # inclusive

    # Map cities to integer IDs for SMT
    city_to_id = {c: i for i, c in enumerate(cities)}
    id_to_city = {i: c for c, i in city_to_id.items()}

    # Allowed direct pairs in ID form
    allowed_pairs = [(city_to_id[a], city_to_id[b]) for (a, b) in direct_flights]

    # SMT Variables
    # 1-based indexing for days
    Loc = [None] + [Int(f"loc_{d}") for d in range(1, days_total + 1)]
    Flight = [None] + [Bool(f"flight_{d}") if d >= 2 else None for d in range(1, days_total + 1)]

    s = Solver()

    # Domain constraints: location each day is one of the cities
    for d in range(1, days_total + 1):
        s.add(Or([Loc[d] == city_to_id[c] for c in cities]))

    # Flight equivalence and direct-flight-only transitions
    for d in range(2, days_total + 1):
        # Flight[d] is true iff location changes from d-1 to d
        s.add(If(Flight[d], Loc[d] != Loc[d - 1], Loc[d] == Loc[d - 1]))
        # If location changes, must be a direct flight
        s.add(Implies(
            Loc[d] != Loc[d - 1],
            Or([And(Loc[d - 1] == a, Loc[d] == b) for (a, b) in allowed_pairs])
        ))

    # City-day counts accounting for double-count on flight days
    # count[c] = sum(Loc[d]==c) + sum_{d>=2}(Flight[d] and Loc[d-1]==c)
    counts = {}
    for c in cities:
        cid = city_to_id[c]
        end_of_day_days = [If(Loc[d] == cid, 1, 0) for d in range(1, days_total + 1)]
        flight_departure_days = [If(And(Flight[d], Loc[d - 1] == cid), 1, 0) for d in range(2, days_total + 1)]
        counts[c] = Sum(end_of_day_days + flight_departure_days)
        s.add(counts[c] == stay_requirements[c])

    # Number of flights equals total city-days minus total days
    total_city_days = sum(stay_requirements.values())
    num_flights = Sum([If(Flight[d], 1, 0) for d in range(2, days_total + 1)])
    s.add(num_flights == total_city_days - days_total)

    # Relatives visit: be in relatives_city on at least one day within the window
    rel_city_id = city_to_id[relatives_city]
    rel_start, rel_end = relatives_window
    in_city_window = []
    for d in range(rel_start, rel_end + 1):
        if d == 1:
            # First day: count presence if end-of-day is the city
            in_city_window.append(Loc[d] == rel_city_id)
        else:
            # Either end-of-day is the city, or it's a flight day from that city
            in_city_window.append(Or(Loc[d] == rel_city_id, And(Flight[d], Loc[d - 1] == rel_city_id)))
    s.add(Or(in_city_window))

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": []}, ensure_ascii=False))
        return

    m = s.model()

    # Extract end-of-day locations
    loc_vals = [None] + [m.eval(Loc[d]).as_long() for d in range(1, days_total + 1)]

    # Build itinerary as contiguous end-of-day segments
    itinerary = []
    start_day = 1
    current_city = loc_vals[1]
    for d in range(2, days_total + 1):
        if loc_vals[d] != current_city:
            itinerary.append({
                "day_range": f"Day {start_day}-{d-1}",
                "place": id_to_city[current_city]
            })
            start_day = d
            current_city = loc_vals[d]
    # Append last segment
    itinerary.append({
        "day_range": f"Day {start_day}-{days_total}",
        "place": id_to_city[current_city]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
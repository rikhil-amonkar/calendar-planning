import json
from z3 import *

def solve_itinerary():
    # Define problem parameters
    total_days = 23
    cities = ["Geneva", "Paris", "Porto", "Oslo", "Reykjavik"]
    city_index = {name: i for i, name in enumerate(cities)}

    # Required days in each city
    required_days = {
        "Paris": 6,
        "Oslo": 5,
        "Porto": 7,
        "Geneva": 7,
        "Reykjavik": 2
    }

    # Direct flights (undirected)
    direct_pairs = [
        ("Paris", "Oslo"),
        ("Geneva", "Oslo"),
        ("Porto", "Paris"),
        ("Geneva", "Paris"),
        ("Geneva", "Porto"),
        ("Paris", "Reykjavik"),
        ("Reykjavik", "Oslo"),
        ("Porto", "Oslo")
    ]
    # Create allowed directed pairs
    allowed_pairs = []
    for (a, b) in direct_pairs:
        ai, bi = city_index[a], city_index[b]
        allowed_pairs.append((ai, bi))
        allowed_pairs.append((bi, ai))

    s = Solver()

    # Variables
    # Start city and End city for each day (0-based index for days)
    Start = [Int(f"Start_{d+1}") for d in range(total_days)]
    End = [Int(f"End_{d+1}") for d in range(total_days)]
    Flight = [Bool(f"Flight_{d+1}") for d in range(total_days)]

    # Domain constraints
    for d in range(total_days):
        s.add(And(Start[d] >= 0, Start[d] < len(cities)))
        s.add(And(End[d] >= 0, End[d] < len(cities)))

    # Temporal continuity: start of day d (d>=2) equals end of day d-1
    for d in range(1, total_days):
        s.add(Start[d] == End[d-1])

    # Flight day relation: flight iff Start != End
    for d in range(total_days):
        s.add(Flight[d] == (Start[d] != End[d]))

    # Direct flights only when there is a flight
    for d in range(total_days):
        # If Flight[d], then (Start[d], End[d]) must be in allowed_pairs
        s.add(Implies(
            Flight[d],
            Or(*[And(Start[d] == ai, End[d] == bi) for (ai, bi) in allowed_pairs])
        ))
        # If not a flight, Start == End is already enforced by Flight[d] == (Start!=End)

    # Presence indicators: Present[c][d] = 1 if city c is present on day d (either start or end)
    Present = [[Int(f"Present_{cities[c]}_{d+1}") for d in range(total_days)] for c in range(len(cities))]
    for c in range(len(cities)):
        for d in range(total_days):
            s.add(Or(Present[c][d] == 0, Present[c][d] == 1))
            s.add(Present[c][d] == If(Or(Start[d] == c, End[d] == c), 1, 0))

    # Sum of present cities per day: 1 if no flight, 2 if flight
    for d in range(total_days):
        s.add(Sum([Present[c][d] for c in range(len(cities))]) == If(Flight[d], 2, 1))

    # City day totals
    for name, req in required_days.items():
        c = city_index[name]
        s.add(Sum([Present[c][d] for d in range(total_days)]) == req)

    # Conference constraints: day 1 and day 7 must include Geneva
    c_geneva = city_index["Geneva"]
    s.add(Present[c_geneva][0] == 1)  # Day 1
    s.add(Present[c_geneva][6] == 1)  # Day 7

    # Oslo relatives: days 19..23 must include Oslo
    c_oslo = city_index["Oslo"]
    for d in range(18, 23):  # indices 18..22
        s.add(Present[c_oslo][d] == 1)

    # Implicitly, required days sum to S = 27 and total_days = 23, hence exactly F=4 flight days.
    # We also enforce that formally:
    flight_ints = [If(Flight[d], 1, 0) for d in range(total_days)]
    total_required = sum(required_days.values())
    s.add(Sum(flight_ints) == total_required - total_days)

    # Solve
    if s.check() != sat:
        return {"itinerary": []}

    m = s.model()

    # Extract flight days (1-based)
    flight_days = []
    for d in range(total_days):
        if is_true(m.eval(Flight[d])):
            flight_days.append(d + 1)

    # Build city sequence: first city is Start[1], then End at each flight day
    seq = []
    first_city = m.eval(Start[0]).as_long()
    seq.append(first_city)
    for fd in flight_days:
        # flight day fd corresponds to zero-based index fd-1
        seq.append(m.eval(End[fd - 1]).as_long())

    # Build itinerary segments with overlapping flight days at boundaries
    itinerary = []
    if len(flight_days) == 0:
        # No flights: single-city trip
        itinerary.append({
            "day_range": f"Day 1-{total_days}",
            "place": cities[seq[0]]
        })
    else:
        # First segment
        itinerary.append({
            "day_range": f"Day 1-{flight_days[0]}",
            "place": cities[seq[0]]
        })
        # Middle segments
        for i in range(1, len(seq) - 1):
            start_day = flight_days[i - 1]
            end_day = flight_days[i]
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": cities[seq[i]]
            })
        # Last segment
        itinerary.append({
            "day_range": f"Day {flight_days[-1]}-{total_days}",
            "place": cities[seq[-1]]
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False))
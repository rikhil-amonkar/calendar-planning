import json
from z3 import Int, Bool, Optimize, Or, And, If, Sum, sat

def main():
    # Cities and indices
    cities = [
        "Salzburg",     # 0
        "Venice",       # 1
        "Bucharest",    # 2
        "Brussels",     # 3
        "Hamburg",      # 4
        "Copenhagen",   # 5
        "Nice",         # 6
        "Zurich",       # 7
        "Naples"        # 8
    ]
    city_to_idx = {name: idx for idx, name in enumerate(cities)}

    # Required durations per city (days counted with overlap on flight days)
    required_days = {
        "Salzburg": 2,
        "Venice": 5,
        "Bucharest": 4,
        "Brussels": 2,
        "Hamburg": 4,
        "Copenhagen": 4,
        "Nice": 3,
        "Zurich": 5,
        "Naples": 4
    }

    # Windows constraints (must be in city at least on one day in the range)
    window_requirements = {
        "Nice": list(range(9, 12)),          # at least one of 9..11
        "Copenhagen": list(range(18, 22)),   # at least one of 18..21
        "Naples": list(range(22, 26)),       # at least one of 22..25
    }
    # Brussels: must be present on both day 21 and day 22
    brussels_days_must = [21, 22]

    # Direct flight edges (undirected)
    edges_text = [
        ("Zurich", "Brussels"),
        ("Bucharest", "Copenhagen"),
        ("Venice", "Brussels"),
        ("Nice", "Zurich"),
        ("Hamburg", "Nice"),
        ("Zurich", "Naples"),
        ("Hamburg", "Bucharest"),
        ("Zurich", "Copenhagen"),
        ("Bucharest", "Brussels"),
        ("Hamburg", "Brussels"),
        ("Venice", "Naples"),
        ("Venice", "Copenhagen"),
        ("Bucharest", "Naples"),
        ("Hamburg", "Copenhagen"),
        ("Venice", "Zurich"),
        ("Nice", "Brussels"),
        ("Hamburg", "Venice"),
        ("Copenhagen", "Naples"),
        ("Nice", "Naples"),
        ("Hamburg", "Zurich"),
        ("Salzburg", "Hamburg"),
        ("Zurich", "Bucharest"),
        ("Brussels", "Naples"),
        ("Copenhagen", "Brussels"),
        ("Venice", "Nice"),
        ("Nice", "Copenhagen"),
    ]
    edges = set()
    for a, b in edges_text:
        ai, bi = city_to_idx[a], city_to_idx[b]
        edges.add((ai, bi))
        edges.add((bi, ai))

    days = list(range(1, 26))  # 1..25
    num_days = len(days)

    # Z3 setup
    opt = Optimize()

    # Variables: Start[d], End[d] for each day (1-based days)
    Start = {d: Int(f"Start_{d}") for d in days}
    End = {d: Int(f"End_{d}") for d in days}

    # Domain constraints
    for d in days:
        opt.add(Start[d] >= 0, Start[d] < len(cities))
        opt.add(End[d] >= 0, End[d] < len(cities))

    # Continuity: End[d] == Start[d+1] for d=1..24
    for d in range(1, 25):
        opt.add(End[d] == Start[d + 1])

    # Flight/day movement constraints: Either stay (Start==End) or allowed direct flight
    def allowed_flight_constraint(d):
        # allowed iff (Start[d], End[d]) in edges, or Start==End
        allowed_pairs = [And(Start[d] == a, End[d] == b) for (a, b) in edges]
        return Or(Start[d] == End[d], Or(allowed_pairs))

    for d in days:
        opt.add(allowed_flight_constraint(d))

    # Day in city boolean: True if city c is either Start[d] or End[d]
    DayInCity = {
        d: {c: Or(Start[d] == c, End[d] == c) for c in range(len(cities))}
        for d in days
    }

    # Duration constraints: exact number of days per city
    for name, req in required_days.items():
        c = city_to_idx[name]
        count = Sum([If(DayInCity[d][c], 1, 0) for d in days])
        opt.add(count == req)

    # Window constraints
    # - Nice (at least one day in 9..11)
    for name, window_days in window_requirements.items():
        c = city_to_idx[name]
        opt.add(Or([DayInCity[d][c] for d in window_days]))

    # - Brussels specifically must be present on both day 21 and day 22
    c_brussels = city_to_idx["Brussels"]
    for d in brussels_days_must:
        opt.add(DayInCity[d][c_brussels])

    # Objective: minimize number of flight days (where Start[d] != End[d])
    flight_bools = [If(Start[d] != End[d], 1, 0) for d in days]
    total_flights = Sum(flight_bools)
    opt.minimize(total_flights)

    # Solve
    if opt.check() != sat:
        # In case of no solution (should not happen), output empty itinerary
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()

    # Extract Start/End cities per day
    start_vals = {d: model.eval(Start[d]).as_long() for d in days}
    end_vals = {d: model.eval(End[d]).as_long() for d in days}

    # Identify flight days (Start != End)
    flight_days = [d for d in days if start_vals[d] != end_vals[d]]

    # Build itinerary segments as overlapping day ranges:
    # Segment 0: Day 1 .. flight_days[0], city = Start[1]
    # Segment i (1..len(flight_days)-1): Day flight_days[i-1] .. flight_days[i], city = End[flight_days[i-1]]
    # Final segment: Day flight_days[-1] .. 25, city = End[flight_days[-1]]
    itinerary = []
    if not flight_days:
        # No flights: entire trip in one city
        city_name = cities[start_vals[1]]
        itinerary.append({"day_range": f"Day 1-25", "place": city_name})
    else:
        # First segment
        first_city = cities[start_vals[1]]
        first_end_day = flight_days[0]
        itinerary.append({"day_range": f"Day 1-{first_end_day}", "place": first_city})

        # Middle segments
        for i in range(1, len(flight_days)):
            seg_start_day = flight_days[i - 1]
            seg_end_day = flight_days[i]
            city_idx = end_vals[flight_days[i - 1]]
            itinerary.append({"day_range": f"Day {seg_start_day}-{seg_end_day}", "place": cities[city_idx]})

        # Final segment
        last_start_day = flight_days[-1]
        last_city = cities[end_vals[flight_days[-1]]]
        itinerary.append({"day_range": f"Day {last_start_day}-25", "place": last_city})

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
import json
from z3 import *

def compute_itinerary():
    # Input variables (trip constraints)
    cities = ["Dublin", "Riga", "Vilnius"]
    city_to_idx = {name: i for i, name in enumerate(cities)}

    total_days = 12
    required_stays = {
        "Riga": 5,
        "Vilnius": 7,
        "Dublin": 2,
    }

    # Directed direct-flight connectivity:
    # - Dublin <-> Riga
    # - Riga -> Vilnius
    direct_flights = {
        (city_to_idx["Dublin"], city_to_idx["Riga"]),
        (city_to_idx["Riga"], city_to_idx["Dublin"]),
        (city_to_idx["Riga"], city_to_idx["Vilnius"]),
    }

    num_segments = 3  # visiting 3 cities as segments

    # Z3 solver
    s = Solver()

    # Segment end days (boundaries)
    e0 = Int('e0')  # end of segment 0
    e1 = Int('e1')  # end of segment 1
    ends = [e0, e1, IntVal(total_days)]

    # Segment start days (derived)
    starts = [IntVal(1), e0, e1]

    # City assignments for each segment (0..2)
    c = [Int(f'c_{i}') for i in range(num_segments)]
    for ci in c:
        s.add(And(ci >= 0, ci < len(cities)))

    # Distinct segments (visit each city exactly once)
    s.add(Distinct(c))

    # Boundary constraints: 1 <= e0 <= e1 <= total_days
    s.add(And(e0 >= 1, e0 <= total_days))
    s.add(And(e1 >= e0, e1 <= total_days))

    # Durations per segment: end - start + 1 (each at least 1 day)
    durations = []
    for i in range(num_segments):
        dur = ends[i] - starts[i] + 1
        durations.append(dur)
        s.add(dur >= 1)

    # Flight constraints between consecutive segments must be direct flights
    for i in range(num_segments - 1):
        allowed_pairs = []
        for (a, b) in direct_flights:
            allowed_pairs.append(And(c[i] == a, c[i + 1] == b))
        s.add(Or(*allowed_pairs))

    # Required stays: sum of durations for each city equals the required days.
    # Note: Travel day overlap is captured by inclusive ranges (starts[i]..ends[i])
    for city_name, req_days in required_stays.items():
        k = city_to_idx[city_name]
        sum_for_city = Sum([If(c[i] == k, durations[i], 0) for i in range(num_segments)])
        s.add(sum_for_city == req_days)

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found given the constraints."}))
        return

    m = s.model()

    # Extract solution
    e0_v = m[e0].as_long()
    e1_v = m[e1].as_long()
    ends_v = [e0_v, e1_v, total_days]
    starts_v = [1, e0_v, e1_v]

    itinerary = []
    for i in range(num_segments):
        city_idx = m[c[i]].as_long()
        itinerary.append({
            "day_range": f"Day {starts_v[i]}-{ends_v[i]}",
            "place": cities[city_idx]
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    compute_itinerary()
import json
from z3 import *

def main():
    # Define cities as an enumeration
    City, (Valencia, Athens, Naples, Zurich) = EnumSort('City', ['Valencia', 'Athens', 'Naples', 'Zurich'])

    # Trip parameters
    total_days = 20
    required_days = {
        Valencia: 6,
        Athens: 6,
        Naples: 5,
        Zurich: 6
    }
    # Windows (inclusive)
    athens_visit_window = (1, 6)
    naples_wedding_window = (16, 20)

    # Allowed directed flights (only direct flights)
    allowed_flights = set([
        (Valencia, Naples), (Naples, Valencia),
        (Valencia, Athens),  # one-way as specified
        (Athens, Naples), (Naples, Athens),
        (Zurich, Naples), (Naples, Zurich),
        (Athens, Zurich), (Zurich, Athens),
        (Zurich, Valencia), (Valencia, Zurich),
    ])

    # Create Z3 variables
    C1, C2, C3, C4 = Consts('C1 C2 C3 C4', City)  # city per segment
    f1, f2, f3 = Ints('f1 f2 f3')                 # flight days (3 flights for 4 segments)

    s = Solver()

    # Flight day constraints (strictly increasing flight days within 1..20)
    s.add(And(1 <= f1, f1 < f2, f2 < f3, f3 <= total_days))

    # Segments: 
    # Segment 1: days [1, f1]
    # Segment 2: days [f1, f2]
    # Segment 3: days [f2, f3]
    # Segment 4: days [f3, 20]
    L1 = f1
    L2 = f2 - f1 + 1
    L3 = f3 - f2 + 1
    L4 = total_days + 1 - f3  # 21 - f3

    # Each segment length must be at least 1
    s.add(L1 >= 1, L2 >= 1, L3 >= 1, L4 >= 1)

    # Exactly 4 distinct cities (visit 4 cities)
    s.add(Distinct(C1, C2, C3, C4))

    # Only allowed direct flights between consecutive segments
    def allowed_edge(src, dst):
        return Or([And(src == a, dst == b) for (a, b) in allowed_flights])

    s.add(allowed_edge(C1, C2))
    s.add(allowed_edge(C2, C3))
    s.add(allowed_edge(C3, C4))

    # Duration constraints per city (sum of segment lengths matching required days)
    # Because C1..C4 are distinct and cover the four cities, this pins each segment's length.
    all_cities = [Valencia, Athens, Naples, Zurich]
    segments = [(C1, L1), (C2, L2), (C3, L3), (C4, L4)]
    for city in all_cities:
        s.add(Sum([If(seg_city == city, seg_len, 0) for seg_city, seg_len in segments]) == required_days[city])

    # Window constraints:
    # Athens must be visited sometime between day 1 and day 6 (inclusive)
    # Naples must be visited sometime between day 16 and day 20 (inclusive)
    # Segment ranges:
    s1_start, s1_end = 1, f1
    s2_start, s2_end = f1, f2
    s3_start, s3_end = f2, f3
    s4_start, s4_end = f3, total_days

    # Helper to assert that a city's segment intersects a target window
    def intersects(city_const, seg_city, seg_start, seg_end, win_start, win_end):
        return And(seg_city == city_const, seg_start <= win_end, seg_end >= win_start)

    s.add(Or(
        intersects(Athens, C1, s1_start, s1_end, athens_visit_window[0], athens_visit_window[1]),
        intersects(Athens, C2, s2_start, s2_end, athens_visit_window[0], athens_visit_window[1]),
        intersects(Athens, C3, s3_start, s3_end, athens_visit_window[0], athens_visit_window[1]),
        intersects(Athens, C4, s4_start, s4_end, athens_visit_window[0], athens_visit_window[1]),
    ))

    s.add(Or(
        intersects(Naples, C1, s1_start, s1_end, naples_wedding_window[0], naples_wedding_window[1]),
        intersects(Naples, C2, s2_start, s2_end, naples_wedding_window[0], naples_wedding_window[1]),
        intersects(Naples, C3, s3_start, s3_end, naples_wedding_window[0], naples_wedding_window[1]),
        intersects(Naples, C4, s4_start, s4_end, naples_wedding_window[0], naples_wedding_window[1]),
    ))

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found under the given constraints."}))
        return

    m = s.model()

    # Extract solution
    f1_val = m.evaluate(f1).as_long()
    f2_val = m.evaluate(f2).as_long()
    f3_val = m.evaluate(f3).as_long()

    def city_to_str(c):
        return str(m.evaluate(c))

    itinerary = [
        {"day_range": f"Day 1-{f1_val}", "place": city_to_str(C1)},
        {"day_range": f"Day {f1_val}-{f2_val}", "place": city_to_str(C2)},
        {"day_range": f"Day {f2_val}-{f3_val}", "place": city_to_str(C3)},
        {"day_range": f"Day {f3_val}-{total_days}", "place": city_to_str(C4)},
    ]

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
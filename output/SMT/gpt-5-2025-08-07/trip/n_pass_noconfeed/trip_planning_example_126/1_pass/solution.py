import json
from z3 import Int, Solver, And, Or, If, Distinct, sat

def main():
    # Input variables (trip constraints)
    total_days = 11
    cities = ["Krakow", "Paris", "Seville"]
    required_days = {
        "Seville": 6,
        "Paris": 2,
        "Krakow": 5
    }
    direct_flights = [
        ("Krakow", "Paris"),
        ("Paris", "Krakow"),
        ("Paris", "Seville"),
        ("Seville", "Paris")
    ]
    workshop_city = "Krakow"
    workshop_window = (1, 5)  # inclusive day range [1, 5]

    # Map cities to indices for SMT
    city_to_idx = {name: i for i, name in enumerate(cities)}
    idx_to_city = {i: name for i, name in enumerate(cities)}
    allowed_pairs = [(city_to_idx[a], city_to_idx[b]) for (a, b) in direct_flights]

    # Z3 variables
    # City order for 3 segments: city1 -> city2 -> city3
    city1 = Int("city1")
    city2 = Int("city2")
    city3 = Int("city3")

    # Day boundaries: segments with overlap on flight days
    end1 = Int("end1")  # Segment 1: [1, end1]
    end2 = Int("end2")  # Segment 2: [end1, end2]
    # Segment 3: [end2, total_days]

    s = Solver()

    # Domain constraints for cities
    s.add(And(city1 >= 0, city1 < len(cities)))
    s.add(And(city2 >= 0, city2 < len(cities)))
    s.add(And(city3 >= 0, city3 < len(cities)))
    s.add(Distinct(city1, city2, city3))

    # Must visit exactly these three cities, with direct flights between transitions
    # Enforce middle city is Paris because only direct links are Krakow-Paris and Paris-Seville
    s.add(city2 == city_to_idx["Paris"])

    # Direct flight constraints between adjacent segments
    s.add(Or(*[And(city1 == a, city2 == b) for (a, b) in allowed_pairs]))
    s.add(Or(*[And(city2 == a, city3 == b) for (a, b) in allowed_pairs]))

    # Day boundary constraints
    s.add(And(end1 >= 1, end1 <= total_days))
    s.add(And(end2 >= end1, end2 <= total_days))

    # Segment lengths (inclusive)
    len1 = end1 - 1 + 1                # = end1
    len2 = end2 - end1 + 1
    len3 = total_days - end2 + 1

    # Required total days per city, counting flight-day overlap
    for city_name, req in required_days.items():
        idx = city_to_idx[city_name]
        s.add(
            (If(city1 == idx, len1, 0) +
             If(city2 == idx, len2, 0) +
             If(city3 == idx, len3, 0)) == req
        )

    # Workshop constraint: must be in workshop_city at least one day within workshop window
    w_start, w_end = workshop_window
    # Intersect-segment condition for the city that equals workshop_city
    s.add(Or(
        And(city1 == city_to_idx[workshop_city], end1 >= w_start, 1 <= w_end),
        And(city2 == city_to_idx[workshop_city], end2 >= w_start, end1 <= w_end),
        And(city3 == city_to_idx[workshop_city], total_days >= w_start, end2 <= w_end)
    ))

    # Solve
    result = {}
    if s.check() == sat:
        m = s.model()
        c1 = idx_to_city[m[city1].as_long()]
        c2 = idx_to_city[m[city2].as_long()]
        c3 = idx_to_city[m[city3].as_long()]
        e1 = m[end1].as_long()
        e2 = m[end2].as_long()

        itinerary = [
            {"day_range": f"Day 1-{e1}", "place": c1},
            {"day_range": f"Day {e1}-{e2}", "place": c2},
            {"day_range": f"Day {e2}-{total_days}", "place": c3},
        ]
        result = {"itinerary": itinerary}
    else:
        # No solution found; return empty itinerary
        result = {"itinerary": []}

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()
import json
from z3 import *

def main():
    # Cities and durations (in days counted with overlaps on flight days)
    cities = [
        "Reykjavik",
        "Stockholm",
        "Porto",
        "Nice",
        "Venice",
        "Vienna",
        "Split",
        "Copenhagen",
    ]
    city_index = {c: i for i, c in enumerate(cities)}

    durations_by_city = {
        "Reykjavik": 2,
        "Stockholm": 2,
        "Porto": 5,
        "Nice": 3,
        "Venice": 4,
        "Vienna": 3,
        "Split": 3,
        "Copenhagen": 2,
    }

    # Days
    DAY_START = 1
    DAY_END = 17

    # Direct flights (undirected)
    direct_pairs = [
        ("Copenhagen", "Vienna"),
        ("Nice", "Stockholm"),
        ("Split", "Copenhagen"),
        ("Nice", "Reykjavik"),
        ("Nice", "Porto"),
        ("Reykjavik", "Vienna"),
        ("Stockholm", "Copenhagen"),
        ("Nice", "Venice"),
        ("Nice", "Vienna"),
        ("Reykjavik", "Copenhagen"),
        ("Nice", "Copenhagen"),
        ("Stockholm", "Vienna"),
        ("Venice", "Vienna"),
        ("Copenhagen", "Venice"),
        ("Vienna", "Porto"),
        ("Copenhagen", "Porto"),
        ("Reykjavik", "Stockholm"),
        ("Stockholm", "Split"),
        ("Split", "Vienna"),
    ]
    # Build adjacency as undirected set of index pairs
    allowed_pairs = set()
    for a, b in direct_pairs:
        ia, ib = city_index[a], city_index[b]
        allowed_pairs.add((ia, ib))
        allowed_pairs.add((ib, ia))

    n = len(cities)

    # Z3 variables
    CityOrder = [Int(f"city_{i}") for i in range(n)]
    start = [Int(f"start_{i}") for i in range(n)]
    end = [Int(f"end_{i}") for i in range(n)]

    s = Solver()

    # Domain constraints for CityOrder: permutation of 0..n-1
    for i in range(n):
        s.add(And(CityOrder[i] >= 0, CityOrder[i] < n))
    s.add(Distinct(CityOrder))

    # Timeline constraints
    s.add(start[0] == DAY_START)
    s.add(end[n-1] == DAY_END)
    for i in range(n):
        s.add(start[i] >= DAY_START)
        s.add(end[i] >= DAY_START)
        s.add(end[i] <= DAY_END)
        s.add(start[i] <= end[i])
    # Overlap exactly one day on transitions
    for i in range(n - 1):
        s.add(start[i + 1] == end[i])

    # Durations per segment depend on which city is at that position
    def duration_expr_for_pos(i):
        # sum of If(city at pos i == c, duration[c], 0) over all cities
        terms = []
        for c in range(n):
            dur = durations_by_city[cities[c]]
            terms.append(If(CityOrder[i] == c, dur, 0))
        return Sum(terms)

    for i in range(n):
        s.add(end[i] - start[i] + 1 == duration_expr_for_pos(i))

    # Direct flight constraints between consecutive cities
    for i in range(n - 1):
        # Or over all allowed pairs that match (CityOrder[i], CityOrder[i+1])
        allowed = []
        for (a, b) in allowed_pairs:
            allowed.append(And(CityOrder[i] == a, CityOrder[i + 1] == b))
        s.add(Or(allowed))

    # Helper for "in city on given day"
    def in_city_on_day(city_name, day):
        cid = city_index[city_name]
        clauses = []
        for i in range(n):
            clauses.append(And(CityOrder[i] == cid, start[i] <= day, day <= end[i]))
        return Or(clauses)

    # Meeting and event constraints
    # Reykjavik between day 3 and day 4 (at least one of those days)
    s.add(Or(in_city_on_day("Reykjavik", 3), in_city_on_day("Reykjavik", 4)))
    # Stockholm between day 4 and day 5
    s.add(Or(in_city_on_day("Stockholm", 4), in_city_on_day("Stockholm", 5)))
    # Vienna workshop between day 11 and day 13
    s.add(Or(in_city_on_day("Vienna", 11), in_city_on_day("Vienna", 12), in_city_on_day("Vienna", 13)))
    # Porto wedding between day 13 and day 17
    s.add(Or(*[in_city_on_day("Porto", d) for d in range(13, 18)]))

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found given the constraints."}))
        return

    m = s.model()

    # Extract solution
    order_ids = [m.evaluate(CityOrder[i]).as_long() for i in range(n)]
    starts = [m.evaluate(start[i]).as_long() for i in range(n)]
    ends = [m.evaluate(end[i]).as_long() for i in range(n)]
    itinerary = []
    for i in range(n):
        place = cities[order_ids[i]]
        day_range = f"Day {starts[i]}-{ends[i]}"
        itinerary.append({"day_range": day_range, "place": place})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
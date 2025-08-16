from z3 import *
import json

def solve_itinerary():
    # Constants
    days = 23
    city_names = ["Paris", "Oslo", "Geneva", "Porto", "Reykjavik"]
    idx = {name: i for i, name in enumerate(city_names)}

    # Requirements
    required_counts = {
        "Paris": 6,
        "Oslo": 5,
        "Geneva": 7,
        "Porto": 7,
        "Reykjavik": 2
    }

    # Direct flights (treat as undirected)
    direct_pairs = {
        ("Paris", "Oslo"),
        ("Geneva", "Oslo"),
        ("Porto", "Paris"),
        ("Geneva", "Paris"),
        ("Geneva", "Porto"),
        ("Paris", "Reykjavik"),
        ("Reykjavik", "Oslo"),
        ("Porto", "Oslo"),
    }
    # Build allowed directed pairs (both directions)
    allowed_directed = set()
    for a, b in direct_pairs:
        allowed_directed.add((idx[a], idx[b]))
        allowed_directed.add((idx[b], idx[a]))

    s = Solver()

    # Variables: city per day (1..23)
    city = [Int(f"city_{d}") for d in range(1, days + 1)]
    for d in range(days):
        s.add(Or([city[d] == i for i in range(len(city_names))]))

    # Flight constraints: if city changes between consecutive days, the pair must be a direct flight
    for d in range(days - 1):
        same_city = city[d] == city[d + 1]
        allowed_change = Or([And(city[d] == a, city[d + 1] == b) for (a, b) in allowed_directed])
        s.add(Or(same_city, allowed_change))

    # InCount[c][d]: boolean that is True iff day d counts for city c according to the rules:
    # Day d counts for city c if:
    #  - You are in city c on day d, OR
    #  - You fly on day d from some city to c (i.e., city[d] != city[d+1] and city[d+1] == c)
    InCount = {
        c: [Bool(f"in_{c}_{d}") for d in range(1, days + 1)]
        for c in range(len(city_names))
    }

    for c in range(len(city_names)):
        for d in range(1, days + 1):
            cond1 = (city[d - 1] == c)
            if d < days:
                cond2 = And(city[d] == c, city[d - 1] != city[d])  # flight on day d (from day d to d+1)
            else:
                cond2 = False  # No flight day after day 23
            s.add(InCount[c][d - 1] == Or(cond1, cond2))

    # City day counts
    for name, req in required_counts.items():
        c = idx[name]
        s.add(Sum([If(InCount[c][d], 1, 0) for d in range(days)]) == req)

    # Oslo must be counted only between day 19 and day 23 inclusive, totaling 5 days
    oslo = idx["Oslo"]
    for d in range(1, days + 1):
        if not (19 <= d <= 23):
            s.add(InCount[oslo][d - 1] == False)
    # The following is implied by total == 5 and outside == False, but we can add it explicitly:
    for d in range(19, 24):
        s.add(InCount[oslo][d - 1] == True)

    # Geneva conference on day 1 and day 7
    geneva = idx["Geneva"]
    s.add(InCount[geneva][0] == True)   # day 1
    s.add(InCount[geneva][6] == True)   # day 7

    # Optional: the total number of flight days equals sum(requirements) - days = 27 - 23 = 4
    flight_days = Sum([If(city[d] != city[d + 1], 1, 0) for d in range(days - 1)])
    s.add(flight_days == (sum(required_counts.values()) - days))

    if s.check() != sat:
        raise RuntimeError("No solution found.")

    m = s.model()

    itinerary = []
    for d in range(1, days + 1):
        c_idx = m[city[d - 1]].as_long()
        itinerary.append({"day": d, "city": city_names[c_idx]})

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    solve_itinerary()
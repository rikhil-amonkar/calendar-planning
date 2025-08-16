from z3 import *
import json

def solve_itinerary():
    # Define cities and mapping
    cities = ["Porto", "Prague", "Reykjavik", "Santorini", "Amsterdam", "Munich"]
    city_to_id = {name: i for i, name in enumerate(cities)}
    id_to_city = {i: name for i, name in enumerate(cities)}

    # Direct flights (undirected)
    direct_pairs = [
        ("Porto", "Amsterdam"),
        ("Munich", "Amsterdam"),
        ("Reykjavik", "Amsterdam"),
        ("Munich", "Porto"),
        ("Prague", "Reykjavik"),
        ("Reykjavik", "Munich"),
        ("Amsterdam", "Santorini"),
        ("Prague", "Amsterdam"),
        ("Prague", "Munich"),
    ]
    edges = set()
    for a, b in direct_pairs:
        u, v = city_to_id[a], city_to_id[b]
        edges.add((u, v))
        edges.add((v, u))

    # Desired total days per city (including flight-day double-counting)
    required = {
        "Porto": 5,
        "Prague": 4,
        "Reykjavik": 4,
        "Santorini": 2,
        "Amsterdam": 2,
        "Munich": 4,
    }
    req = [required[name] for name in cities]

    D = 16  # total days
    # Variables: city[d] is the city at end of day d (1-based days; we store 0..D-1)
    city = [Int(f"city_{d+1}") for d in range(D)]

    s = Solver()

    # Domain constraints
    for d in range(D):
        s.add(And(city[d] >= 0, city[d] < len(cities)))

    # Movement constraints: either stay or take a direct flight between days
    for d in range(1, D):
        u = city[d - 1]
        v = city[d]
        allowed_transitions = [u == v] + [And(u == a, v == b) for (a, b) in edges]
        s.add(Or(*allowed_transitions))

    # Contribution expression: day d contributes to city c if
    # - current city on day d is c, OR
    # - d >= 2 and it's a flight day and previous city on day d-1 was c (i.e., leaving c on day d)
    def contributes(c, d):  # c is int city id, d is 1..D
        cur = If(city[d - 1] == c, 1, 0)
        if d == 1:
            prev_flight = 0
        else:
            prev_flight = If(And(city[d - 2] == c, city[d - 1] != city[d - 2]), 1, 0)
        return cur + prev_flight  # always 0 or 1

    # Total required days per city (including flight-day double-counting)
    for c in range(len(cities)):
        s.add(Sum([contributes(c, d + 1) for d in range(D)]) == req[c])

    # Wedding in Reykjavik between day 4 and day 7 (inclusive): at least one of these days contributes to Reykjavik
    rvk = city_to_id["Reykjavik"]
    s.add(Or(*[contributes(rvk, d) == 1 for d in range(4, 8)]))

    # Conference in Amsterdam on day 14 and day 15: both days contribute to Amsterdam
    ams = city_to_id["Amsterdam"]
    s.add(contributes(ams, 14) == 1)
    s.add(contributes(ams, 15) == 1)
    # Combined with total Amsterdam == 2, this ensures only these two days count for Amsterdam.

    # Meet friend in Munich between day 7 and day 10 (inclusive): at least one day contributes to Munich
    muc = city_to_id["Munich"]
    s.add(Or(*[contributes(muc, d) == 1 for d in range(7, 11)]))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Build itinerary as list of day/place mappings
    itinerary = []
    for d in range(D):
        city_id = m[city[d]].as_long()
        itinerary.append({"day": d + 1, "place": id_to_city[city_id]})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result))
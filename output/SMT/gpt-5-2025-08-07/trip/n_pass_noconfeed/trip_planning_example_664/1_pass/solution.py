import json
from z3 import *

def main():
    # Define cities and mapping
    cities = ["Tallinn", "Bucharest", "Seville", "Stockholm", "Munich", "Milan"]
    idx = {name: i for i, name in enumerate(cities)}

    # Required total days (presence-days) per city
    req_days = {
        idx["Tallinn"]: 2,
        idx["Bucharest"]: 4,
        idx["Seville"]: 5,
        idx["Stockholm"]: 5,
        idx["Munich"]: 5,
        idx["Milan"]: 2,
    }

    total_days = 18
    segments = 6  # visiting 6 cities exactly once implies 6 segments and 5 transitions

    # Direct flight graph (undirected), construct directed pairs for constraints
    edges_undirected = [
        ("Milan", "Stockholm"),
        ("Munich", "Stockholm"),
        ("Bucharest", "Munich"),
        ("Munich", "Seville"),
        ("Stockholm", "Tallinn"),
        ("Munich", "Milan"),
        ("Munich", "Tallinn"),
        ("Seville", "Milan"),
    ]
    allowed_directed = []
    for a, b in edges_undirected:
        allowed_directed.append((idx[a], idx[b]))
        allowed_directed.append((idx[b], idx[a]))

    # Z3 variables
    seg_city = [Int(f"seg_city_{i}") for i in range(segments)]
    seg_len = [Int(f"seg_len_{i}") for i in range(segments)]
    start = [Int(f"start_{i}") for i in range(segments)]

    s = Solver()

    # Domains for seg_city and seg_len
    for i in range(segments):
        s.add(And(seg_city[i] >= 0, seg_city[i] < len(cities)))
        s.add(seg_len[i] >= 1)

    # Each city visited exactly once (6 distinct cities)
    s.add(Distinct(*seg_city))

    # Start day constraints
    s.add(start[0] == 1)
    for i in range(1, segments):
        s.add(start[i] == start[i - 1] + seg_len[i - 1])

    # End day must be 18
    s.add(start[segments - 1] + seg_len[segments - 1] - 1 == total_days)

    # Adjacency (direct flights) between consecutive segments
    for i in range(1, segments):
        ors = []
        for (a, b) in allowed_directed:
            ors.append(And(seg_city[i - 1] == a, seg_city[i] == b))
        s.add(Or(*ors))

    # Duration constraints derived from presence counting rule:
    # Presence days for city in segment i = seg_len[i] + (1 if i < last else 0)
    for i in range(segments):
        extra = 1 if i < segments - 1 else 0
        for c in range(len(cities)):
            s.add(Implies(seg_city[i] == c, seg_len[i] == req_days[c] - extra))

    # Helper to compute presence of city c on day d
    def presence_literal(c_idx, d):
        ors = []
        for i in range(segments):
            # Days ended in city during its segment
            in_segment = And(seg_city[i] == c_idx, start[i] <= d, d <= start[i] + seg_len[i] - 1)
            ors.append(in_segment)
            # Departure day to next segment counts previous city presence (if not last segment)
            if i < segments - 1:
                departure_day = And(seg_city[i] == c_idx, d == start[i] + seg_len[i])
                ors.append(departure_day)
        return Or(*ors)

    # Event windows:
    # - Visit relatives in Bucharest between day 1 and day 4 (presence on at least one of these days)
    # - Meet friends in Seville between day 8 and day 12
    # - Attend wedding in Munich between day 4 and day 8
    def window_constraint(city_name, start_day, end_day):
        c = idx[city_name]
        days = [presence_literal(c, d) for d in range(start_day, end_day + 1)]
        s.add(Or(*days))

    window_constraint("Bucharest", 1, 4)
    window_constraint("Seville", 8, 12)
    window_constraint("Munich", 4, 8)

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = s.model()

    # Extract segments and build itinerary
    segs = []
    for i in range(segments):
        c = m.evaluate(seg_city[i]).as_long()
        L = m.evaluate(seg_len[i]).as_long()
        Sday = m.evaluate(start[i]).as_long()
        Eday = Sday + L - 1
        segs.append((Sday, Eday, cities[c]))

    # Sort segments by start day just in case (they should already be ordered)
    segs.sort(key=lambda x: x[0])

    itinerary = []
    for Sday, Eday, place in segs:
        itinerary.append({
            "day_range": f"Day {Sday}-{Eday}",
            "place": place
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
import json
from z3 import *

def solve_itinerary():
    # Define cities
    cities = ["Berlin", "Nice", "Athens", "Stockholm", "Barcelona", "Vilnius", "Lyon"]
    city_id = {c: i for i, c in enumerate(cities)}
    n_cities = len(cities)
    total_days = 20

    # Desired durations per city
    durations = {
        "Berlin": 3,
        "Nice": 5,
        "Athens": 5,
        "Stockholm": 5,
        "Barcelona": 2,
        "Vilnius": 4,
        "Lyon": 2,
    }

    # Undirected direct flight connections
    undirected_edges = [
        ("Lyon", "Nice"),
        ("Stockholm", "Athens"),
        ("Nice", "Athens"),
        ("Berlin", "Athens"),
        ("Berlin", "Nice"),
        ("Berlin", "Barcelona"),
        ("Berlin", "Vilnius"),
        ("Barcelona", "Nice"),
        ("Athens", "Vilnius"),
        ("Berlin", "Stockholm"),
        ("Nice", "Stockholm"),
        ("Barcelona", "Athens"),
        ("Barcelona", "Stockholm"),
        ("Barcelona", "Lyon"),
    ]

    # Build directed edges for convenience
    directed_edges = []
    for a, b in undirected_edges:
        directed_edges.append((city_id[a], city_id[b]))
        directed_edges.append((city_id[b], city_id[a]))

    # SMT variables for 7 segments (one per city, unique)
    seg_city = [Int(f"seg_city_{i}") for i in range(n_cities)]
    seg_start = [Int(f"seg_start_{i}") for i in range(n_cities)]
    seg_end = [Int(f"seg_end_{i}") for i in range(n_cities)]
    seg_len = [Int(f"seg_len_{i}") for i in range(n_cities)]

    s = Solver()

    # Domains
    for i in range(n_cities):
        s.add(seg_city[i] >= 0, seg_city[i] < n_cities)
        s.add(seg_start[i] >= 1, seg_start[i] <= total_days)
        s.add(seg_end[i] >= 1, seg_end[i] <= total_days)
        s.add(seg_len[i] == seg_end[i] - seg_start[i] + 1)
        s.add(seg_start[i] <= seg_end[i])

    # Each segment mapped to a unique city
    s.add(Distinct(seg_city))

    # Each segment length must equal the required duration of the city assigned to it
    for i in range(n_cities):
        choices = []
        for cname, cid in city_id.items():
            choices.append(And(seg_city[i] == cid, seg_len[i] == durations[cname]))
        s.add(Or(choices))

    # Chain constraints with overlaps on flight days:
    # - Trip spans day 1..20
    # - seg_start[0] == 1
    # - seg_end[6] == 20
    # - For i>0: seg_start[i] == seg_end[i-1]
    s.add(seg_start[0] == 1)
    s.add(seg_end[-1] == total_days)
    for i in range(1, n_cities):
        s.add(seg_start[i] == seg_end[i - 1])

    # Direct flight constraint between consecutive segments
    for i in range(1, n_cities):
        allowed = [And(seg_city[i - 1] == a, seg_city[i] == b) for (a, b) in directed_edges]
        s.add(Or(allowed))

    # Event constraints:
    # Berlin: conference on Day 1 and Day 3
    for i in range(n_cities):
        s.add(Implies(seg_city[i] == city_id["Berlin"], And(seg_start[i] <= 1, 1 <= seg_end[i])))
        s.add(Implies(seg_city[i] == city_id["Berlin"], And(seg_start[i] <= 3, 3 <= seg_end[i])))

    # Barcelona: workshop between Day 3 and Day 4 (in Barcelona on days 3 and 4)
    for i in range(n_cities):
        s.add(Implies(seg_city[i] == city_id["Barcelona"], And(seg_start[i] <= 3, 3 <= seg_end[i])))
        s.add(Implies(seg_city[i] == city_id["Barcelona"], And(seg_start[i] <= 4, 4 <= seg_end[i])))

    # Lyon: wedding between Day 4 and Day 5 (in Lyon on days 4 and 5)
    for i in range(n_cities):
        s.add(Implies(seg_city[i] == city_id["Lyon"], And(seg_start[i] <= 4, 4 <= seg_end[i])))
        s.add(Implies(seg_city[i] == city_id["Lyon"], And(seg_start[i] <= 5, 5 <= seg_end[i])))

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found."}))
        return

    m = s.model()

    # Extract segments
    segments = []
    for i in range(n_cities):
        c = m[seg_city[i]].as_long()
        start = m[seg_start[i]].as_long()
        end = m[seg_end[i]].as_long()
        segments.append((start, end, cities[c]))

    # Sort by start day (though already ordered due to chain)
    segments.sort(key=lambda x: x[0])

    itinerary = []
    for (st, en, place) in segments:
        itinerary.append({"day_range": f"Day {st}-{en}", "place": place})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    solve_itinerary()
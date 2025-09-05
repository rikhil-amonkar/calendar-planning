import json
from z3 import *

def main():
    # Define cities
    cities = ["Brussels", "Rome", "Dubrovnik", "Geneva", "Budapest", "Riga", "Valencia"]
    B, Rm, Dbv, Gnv, Bp, Rg, Vlc = range(len(cities))

    # Required durations per city
    duration_by_city = {
        B: 5,   # Brussels
        Rm: 2,  # Rome
        Dbv: 3, # Dubrovnik
        Gnv: 5, # Geneva
        Bp: 2,  # Budapest
        Rg: 4,  # Riga
        Vlc: 2  # Valencia
    }

    # Build directed adjacency (direct flights)
    # "and" -> both directions, "from X to Y" -> one direction
    directed_edges = set()

    def add_undirected(a, b):
        directed_edges.add((a, b))
        directed_edges.add((b, a))

    def add_directed(a, b):
        directed_edges.add((a, b))

    # Given direct flights:
    add_undirected(B, Vlc)   # Brussels and Valencia
    add_undirected(Rm, Vlc)  # Rome and Valencia
    add_undirected(B, Gnv)   # Brussels and Geneva
    add_undirected(Rm, Gnv)  # Rome and Geneva
    add_undirected(Dbv, Gnv) # Dubrovnik and Geneva
    add_undirected(Vlc, Gnv) # Valencia and Geneva
    add_directed(Rm, Rg)     # from Rome to Riga
    add_undirected(Rg, B)    # Riga and Brussels
    add_undirected(Gnv, Bp)  # Geneva and Budapest
    add_undirected(Rm, Bp)   # Rome and Budapest
    add_undirected(Rm, B)    # Rome and Brussels
    add_undirected(B, Bp)    # Brussels and Budapest
    add_undirected(Dbv, Rm)  # Dubrovnik and Rome

    # SMT variables
    k = 7  # number of segments/cities to visit
    city_vars = [Int(f"city_{i}") for i in range(k)]
    start_vars = [Int(f"start_{i}") for i in range(k)]
    end_vars = [Int(f"end_{i}") for i in range(k)]
    dur_vars = [Int(f"dur_{i}") for i in range(k)]

    s = Solver()

    # Domains
    for i in range(k):
        s.add(city_vars[i] >= 0, city_vars[i] < len(cities))
        s.add(start_vars[i] >= 1, start_vars[i] <= 17)
        s.add(end_vars[i] >= 1, end_vars[i] <= 17)

    # Each city exactly once (permutation of 0..6)
    s.add(Distinct(city_vars))

    # Duration per segment matches chosen city
    for i in range(k):
        s.add(dur_vars[i] == Sum([If(city_vars[i] == c, duration_by_city[c], 0) for c in range(len(cities))]))
        s.add(end_vars[i] == start_vars[i] + dur_vars[i] - 1)

    # Timeline chaining with overlap on travel days
    s.add(start_vars[0] == 1)
    for i in range(1, k):
        s.add(start_vars[i] == end_vars[i - 1])

    # Total must end at day 17 (redundant given durations but explicit)
    s.add(end_vars[k - 1] == 17)

    # Direct flights constraint between consecutive segments
    allowed_pairs = list(directed_edges)
    for i in range(k - 1):
        s.add(Or([And(city_vars[i] == a, city_vars[i + 1] == b) for (a, b) in allowed_pairs]))

    # City-specific constraints:
    # Brussels: exactly days 7-11 (5 days) to attend workshop between day 7 and 11
    for i in range(k):
        s.add(Implies(city_vars[i] == B, And(start_vars[i] == 7, end_vars[i] == 11)))

    # Riga: meet friends between day 4 and day 7 (at least one day overlap)
    for i in range(k):
        s.add(Implies(city_vars[i] == Rg, And(start_vars[i] <= 7, end_vars[i] >= 4)))

    # Budapest: meet a friend between day 16 and day 17 (at least one day overlap)
    for i in range(k):
        s.add(Implies(city_vars[i] == Bp, And(start_vars[i] <= 17, end_vars[i] >= 16)))

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    m = s.model()

    # Extract solution
    itinerary = []
    for i in range(k):
        city_idx = m[city_vars[i]].as_long()
        start_day = m[start_vars[i]].as_long()
        end_day = m[end_vars[i]].as_long()
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": cities[city_idx]
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
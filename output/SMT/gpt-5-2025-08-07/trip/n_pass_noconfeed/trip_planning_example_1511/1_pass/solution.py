import json
from z3 import *

def main():
    # Define cities and mapping
    cities = ["Venice", "Reykjavik", "Munich", "Santorini", "Manchester", "Porto", "Bucharest", "Tallinn", "Valencia", "Vienna"]
    city_index = {c: i for i, c in enumerate(cities)}
    
    # Durations per city
    durations = {
        "Venice": 3,
        "Reykjavik": 2,
        "Munich": 3,
        "Santorini": 3,
        "Manchester": 3,
        "Porto": 3,
        "Bucharest": 5,
        "Tallinn": 4,
        "Valencia": 2,
        "Vienna": 5
    }
    
    # Anchored stays (inclusive day ranges)
    anchors = {
        "Munich": (4, 6),
        "Santorini": (8, 10),
        "Valencia": (14, 15)
    }
    
    # Direct flight pairs (undirected)
    direct_pairs = [
        ("Bucharest", "Manchester"),
        ("Munich", "Venice"),
        ("Santorini", "Manchester"),
        ("Vienna", "Reykjavik"),
        ("Venice", "Santorini"),
        ("Munich", "Porto"),
        ("Valencia", "Vienna"),
        ("Manchester", "Vienna"),
        ("Porto", "Vienna"),
        ("Venice", "Manchester"),
        ("Santorini", "Vienna"),
        ("Munich", "Manchester"),
        ("Munich", "Reykjavik"),
        ("Bucharest", "Valencia"),
        ("Venice", "Vienna"),
        ("Bucharest", "Vienna"),
        ("Porto", "Manchester"),
        ("Munich", "Vienna"),
        ("Valencia", "Porto"),
        ("Munich", "Bucharest"),
        ("Tallinn", "Munich"),
        ("Santorini", "Bucharest"),
        ("Munich", "Valencia")
    ]
    
    # Build adjacency set (both directions)
    n = len(cities)
    adj = [[False]*n for _ in range(n)]
    for a, b in direct_pairs:
        i = city_index[a]
        j = city_index[b]
        adj[i][j] = True
        adj[j][i] = True
    
    # Z3 variables
    segments = 10  # number of city segments (visit each city once)
    city_vars = [Int(f"city_{i}") for i in range(segments)]
    S_vars = [Int(f"S_{i}") for i in range(segments)]  # start day inclusive
    E_vars = [Int(f"E_{i}") for i in range(segments)]  # end day inclusive
    L_vars = [Int(f"L_{i}") for i in range(segments)]  # length
    
    s = Solver()
    
    # Domains
    for i in range(segments):
        s.add(And(city_vars[i] >= 0, city_vars[i] < n))
        s.add(And(S_vars[i] >= 1, S_vars[i] <= 24))
        s.add(And(E_vars[i] >= 1, E_vars[i] <= 24))
        s.add(L_vars[i] >= 1)
    
    # All cities are distinct -> permutation of all cities
    s.add(Distinct(city_vars))
    
    # Segment chaining with 1-day overlap between consecutive segments
    s.add(S_vars[0] == 1)       # trip starts day 1
    s.add(E_vars[-1] == 24)     # trip ends day 24
    for i in range(segments):
        # Map length from city
        len_expr = None
        for c_name, cid in city_index.items():
            term = If(city_vars[i] == cid, durations[c_name], 0)
            len_expr = term if len_expr is None else len_expr + term
        s.add(L_vars[i] == len_expr)
        s.add(E_vars[i] == S_vars[i] + L_vars[i] - 1)
        if i > 0:
            # Overlap day: start of this equals end of previous
            s.add(S_vars[i] == E_vars[i-1])
    
    # Connectivity constraints: direct flight between consecutive segments
    for i in range(segments - 1):
        allowed = []
        for a in range(n):
            for b in range(n):
                if adj[a][b]:
                    allowed.append(And(city_vars[i] == a, city_vars[i+1] == b))
        s.add(Or(allowed))
    
    # Anchor constraints
    for i in range(segments):
        for cname, (a_start, a_end) in anchors.items():
            cid = city_index[cname]
            s.add(Implies(city_vars[i] == cid, And(S_vars[i] == a_start, E_vars[i] == a_end)))
    
    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": [], "status": "unsat"}))
        return
    m = s.model()
    
    itinerary = []
    for i in range(segments):
        c_id = m.eval(city_vars[i]).as_long()
        start = m.eval(S_vars[i]).as_long()
        end = m.eval(E_vars[i]).as_long()
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": cities[c_id]
        })
    
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
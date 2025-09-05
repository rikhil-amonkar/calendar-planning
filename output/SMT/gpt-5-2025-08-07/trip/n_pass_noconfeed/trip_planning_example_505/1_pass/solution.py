import json
from z3 import Int, Bool, If, And, Or, Optimize, Sum, sat

def main():
    # Input parameters and constraints
    cities = ["Prague", "Stuttgart", "Split", "Krakow", "Florence"]
    idx = {name: i for i, name in enumerate(cities)}
    n_days = 8

    # Desired stays (days count where presence includes start or end city)
    desired_stays = {
        "Prague": 4,
        "Stuttgart": 2,
        "Split": 2,
        "Krakow": 2,
        "Florence": 2,
    }

    # Events:
    # - Wedding in Stuttgart between day 2 and 3 -> must be in Stuttgart on day 2 or day 3
    wedding_city = "Stuttgart"
    wedding_day_range = (2, 3)

    # - Meet friends in Split between day 3 and 4 -> must be in Split on day 3 or day 4
    friends_city = "Split"
    friends_day_range = (3, 4)

    # Direct flight adjacency (undirected)
    direct_pairs = [
        ("Stuttgart", "Split"),
        ("Prague", "Florence"),
        ("Krakow", "Stuttgart"),
        ("Krakow", "Split"),
        ("Split", "Prague"),
        ("Krakow", "Prague"),
    ]
    # Convert to index pairs (both directions)
    allowed_edges = set()
    for a, b in direct_pairs:
        ai, bi = idx[a], idx[b]
        allowed_edges.add((ai, bi))
        allowed_edges.add((bi, ai))

    # Z3 variables
    c_end = [Int(f"c_end_{d}") for d in range(1, n_days + 1)]  # end-of-day city for day d
    c0 = Int("c0")  # start-of-day city for day 1 (before any flight)
    flight = [Bool(f"flight_{d}") for d in range(1, n_days + 1)]

    opt = Optimize()

    # Domain constraints
    for v in c_end + [c0]:
        opt.add(And(v >= 0, v < len(cities)))

    # Start city and transitions
    # flight[1] <-> (c0 != c_end[1])
    opt.add(flight[0] == (c0 != c_end[0]))
    # For d >= 2: flight[d] <-> (c_end[d-1] != c_end[d])
    for d in range(2, n_days + 1):
        opt.add(flight[d - 1] == (c_end[d - 2] != c_end[d - 1]))

    # Helper to get start city expression for each day
    def start_city_expr(day_idx):
        # day_idx is 1-based
        return c0 if day_idx == 1 else c_end[day_idx - 2]

    # Direct flight constraint: if a flight occurs on day d, it must be along an allowed edge
    for d in range(1, n_days + 1):
        s = start_city_expr(d)
        e = c_end[d - 1]
        # Build Or over allowed edges: (s==a and e==b) for any (a,b) in allowed_edges
        edge_ok = Or(*[And(s == a, e == b) for (a, b) in allowed_edges]) if allowed_edges else False
        opt.add(Or(Or(flight[d - 1]) == False, edge_ok))

    # Presence calculation: presence_in_city[city][day] = start_city(day) == city OR end_city(day) == city
    presence = {}
    for cname in cities:
        cidx = idx[cname]
        presence[cname] = []
        for d in range(1, n_days + 1):
            s = start_city_expr(d)
            e = c_end[d - 1]
            pres = Or(s == cidx, e == cidx)
            presence[cname].append(pres)

    # Duration constraints: exact stays per city
    for cname, target in desired_stays.items():
        pres_sum = Sum([If(pres, 1, 0) for pres in presence[cname]])
        opt.add(pres_sum == target)

    # Event constraints
    # Wedding in Stuttgart on day 2 or 3
    opt.add(Or(presence[wedding_city][wedding_day_range[0] - 1],
               presence[wedding_city][wedding_day_range[1] - 1]))
    # Friends meeting in Split on day 3 or 4
    opt.add(Or(presence[friends_city][friends_day_range[0] - 1],
               presence[friends_city][friends_day_range[1] - 1]))

    # Ensure we visit all five cities (redundant given exact durations, but explicit)
    for cname in cities:
        opt.add(Sum([If(pres, 1, 0) for pres in presence[cname]]) >= 1)

    # Optional: minimize number of flights (should be 4 given totals)
    total_flights = Sum([If(f, 1, 0) for f in flight])
    opt.minimize(total_flights)

    # Solve
    if opt.check() != sat:
        # Fallback JSON with empty itinerary if unsat (should not happen for given constraints)
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()

    # Extract end-of-day cities
    end_seq = [model[c_end[d]].as_long() for d in range(n_days)]
    # We can also extract flight info if needed
    # flights_seq = [model[flight[d]].is_true() for d in range(n_days)]

    # Build contiguous end-of-day segments as itinerary
    itinerary = []
    current_city = end_seq[0]
    start_day = 1
    for day in range(2, n_days + 1):
        if end_seq[day - 1] != current_city:
            itinerary.append({
                "day_range": f"Day {start_day}-{day - 1}",
                "place": cities[current_city]
            })
            current_city = end_seq[day - 1]
            start_day = day
    # Append last segment
    itinerary.append({
        "day_range": f"Day {start_day}-{n_days}",
        "place": cities[current_city]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
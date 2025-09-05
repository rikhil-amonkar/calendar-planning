import json
from z3 import *

def main():
    # Problem data (treated as input variables)
    days_total = 22
    cities = ["Berlin", "Split", "Bucharest", "Riga", "Lisbon", "Tallinn", "Lyon"]
    city_idx = {c: i for i, c in enumerate(cities)}
    N = len(cities)

    # Desired exact stay counts per city (counts include flight days if present)
    required_days = {
        "Berlin": 5,
        "Split": 3,
        "Bucharest": 3,
        "Riga": 5,
        "Lisbon": 3,
        "Tallinn": 4,
        "Lyon": 5,
    }

    # Fixed presence windows (inclusive) where traveler must be present in that city
    # Days are 1-indexed
    must_be_in = {
        "Berlin": [(1, 5)],     # annual show
        "Lyon": [(7, 11)],      # wedding
        "Bucharest": [(13, 15)] # visit relatives
    }

    # Direct flight graph (directed). For "A and B" we add both directions.
    edges = set()
    def add_undirected(a, b):
        edges.add((city_idx[a], city_idx[b]))
        edges.add((city_idx[b], city_idx[a]))
    def add_directed(a, b):
        edges.add((city_idx[a], city_idx[b]))

    add_undirected("Lisbon", "Bucharest")
    add_undirected("Berlin", "Lisbon")
    add_undirected("Bucharest", "Riga")
    add_undirected("Berlin", "Riga")
    add_undirected("Split", "Lyon")
    add_undirected("Lisbon", "Riga")
    add_directed("Riga", "Tallinn")  # directed only
    add_undirected("Berlin", "Split")
    add_undirected("Lyon", "Lisbon")
    add_undirected("Berlin", "Tallinn")
    add_undirected("Lyon", "Bucharest")

    # Z3 variables
    # loc_day[d]: city index where we start day d (1..days_total)
    loc_day = {d: Int(f"loc_{d}") for d in range(1, days_total + 1)}
    # fly_day[d]: whether we take a flight on day d
    fly_day = {d: Bool(f"fly_{d}") for d in range(1, days_total + 1)}
    # dest_day[d]: destination city index if we fly on day d (otherwise equal to loc_day[d])
    dest_day = {d: Int(f"dest_{d}") for d in range(1, days_total + 1)}

    s = Optimize()

    # Domain constraints
    for d in range(1, days_total + 1):
        s.add(And(loc_day[d] >= 0, loc_day[d] < N))
        s.add(And(dest_day[d] >= 0, dest_day[d] < N))

    # Movement constraints
    for d in range(1, days_total + 1):
        # If flying, must use a direct flight to some other city
        # If not flying, dest = loc (no movement that day)
        s.add(Implies(Not(fly_day[d]), dest_day[d] == loc_day[d]))
        # If flying, destination different and edge must exist
        s.add(Implies(fly_day[d],
                      And(dest_day[d] != loc_day[d],
                          Or([And(loc_day[d] == i, dest_day[d] == j) for (i, j) in edges]))))
        # Transition to next day's location
        if d < days_total:
            s.add(loc_day[d + 1] == If(fly_day[d], dest_day[d], loc_day[d]))

    # Presence tracking: present[c][d] is True if city c is visited on day d
    present = {
        c: {d: Bool(f"present_{c}_{d}") for d in range(1, days_total + 1)}
        for c in range(N)
    }
    for d in range(1, days_total + 1):
        for c in range(N):
            s.add(present[c][d] == Or(loc_day[d] == c, And(fly_day[d], dest_day[d] == c)))

    # Exact day-count constraints per city
    for cname, req in required_days.items():
        c = city_idx[cname]
        s.add(Sum([If(present[c][d], 1, 0) for d in range(1, days_total + 1)]) == req)

    # Fixed presence windows
    for cname, intervals in must_be_in.items():
        c = city_idx[cname]
        for (a, b) in intervals:
            for d in range(a, b + 1):
                s.add(present[c][d])

    # Optional: make the plan "optimal" by minimizing total number of flight days
    total_flights = Sum([If(fly_day[d], 1, 0) for d in range(1, days_total + 1)])
    s.minimize(total_flights)

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    m = s.model()

    # Extract solution
    loc = {d: m.evaluate(loc_day[d]).as_long() for d in range(1, days_total + 1)}
    fly = {d: is_true(m.evaluate(fly_day[d])) for d in range(1, days_total + 1)}
    dest = {d: m.evaluate(dest_day[d]).as_long() for d in range(1, days_total + 1)}

    # Compute presence sets by day
    day_presence = []
    for d in range(1, days_total + 1):
        ps = set()
        ps.add(loc[d])
        if fly[d]:
            ps.add(dest[d])
        # Convert to sorted list of city names
        names = sorted([cities[i] for i in ps])
        day_presence.append(names)

    # Compress into contiguous segments with same presence set
    segments = []
    start = 1
    prev = day_presence[0]
    for d in range(2, days_total + 1):
        if day_presence[d - 1] != prev:
            segments.append((start, d - 1, prev))
            start = d
            prev = day_presence[d - 1]
        prev = day_presence[d - 1]
    # Append last segment
    segments.append((start, days_total, day_presence[-1]))

    # But the loop above handled prev incorrectly for equal segments; fix compression properly
    segments = []
    start = 1
    prev_set = day_presence[0]
    for d in range(2, days_total + 1):
        if day_presence[d - 1] != prev_set:
            segments.append((start, d - 1, prev_set))
            start = d
            prev_set = day_presence[d - 1]
        else:
            # same set, continue
            pass
    # add final
    segments.append((start, days_total, prev_set))

    # Build JSON itinerary
    itinerary = []
    for (a, b, names) in segments:
        place_str = ", ".join(names)
        itinerary.append({
            "day_range": f"Day {a}-{b}",
            "place": place_str
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
import json
from z3 import *

def main():
    # Cities (10 total)
    cities = [
        "Prague", "Brussels", "Riga", "Munich", "Seville",
        "Stockholm", "Istanbul", "Amsterdam", "Vienna", "Split"
    ]
    idx = {name: i for i, name in enumerate(cities)}

    # Directed flight graph construction
    # "A and B" means bidirectional edges; "from A to B" means directed A->B
    def add_bidirectional(edges, a, b):
        edges.add((idx[a], idx[b]))
        edges.add((idx[b], idx[a]))

    def add_directed(edges, a, b):
        edges.add((idx[a], idx[b]))

    edges = set()
    # Given direct flights list:
    add_bidirectional(edges, "Riga", "Stockholm")
    add_bidirectional(edges, "Stockholm", "Brussels")
    add_bidirectional(edges, "Istanbul", "Munich")
    add_bidirectional(edges, "Istanbul", "Riga")
    add_bidirectional(edges, "Prague", "Split")
    add_bidirectional(edges, "Vienna", "Brussels")
    add_bidirectional(edges, "Vienna", "Riga")
    add_bidirectional(edges, "Split", "Stockholm")
    add_bidirectional(edges, "Munich", "Amsterdam")
    add_bidirectional(edges, "Split", "Amsterdam")
    add_bidirectional(edges, "Amsterdam", "Stockholm")
    add_bidirectional(edges, "Amsterdam", "Riga")
    add_bidirectional(edges, "Vienna", "Stockholm")
    add_bidirectional(edges, "Vienna", "Istanbul")
    add_bidirectional(edges, "Vienna", "Seville")
    add_bidirectional(edges, "Istanbul", "Amsterdam")
    add_bidirectional(edges, "Munich", "Brussels")
    add_bidirectional(edges, "Prague", "Munich")
    add_directed(edges, "Riga", "Munich")  # directed only Riga -> Munich
    add_bidirectional(edges, "Prague", "Amsterdam")
    add_bidirectional(edges, "Prague", "Brussels")
    add_bidirectional(edges, "Prague", "Istanbul")
    add_bidirectional(edges, "Istanbul", "Stockholm")
    add_bidirectional(edges, "Vienna", "Prague")
    add_bidirectional(edges, "Munich", "Split")
    add_bidirectional(edges, "Vienna", "Amsterdam")
    add_bidirectional(edges, "Prague", "Stockholm")
    add_bidirectional(edges, "Brussels", "Seville")
    add_bidirectional(edges, "Munich", "Stockholm")
    add_bidirectional(edges, "Istanbul", "Brussels")
    add_bidirectional(edges, "Amsterdam", "Seville")
    add_bidirectional(edges, "Vienna", "Split")
    add_bidirectional(edges, "Munich", "Seville")
    add_bidirectional(edges, "Riga", "Brussels")
    add_bidirectional(edges, "Prague", "Riga")
    add_bidirectional(edges, "Vienna", "Munich")

    n_days = 20
    Days = range(1, n_days + 1)
    C = len(cities)

    # Z3 variables
    start_city = [Int(f"start_{d}") for d in Days]
    end_city   = [Int(f"end_{d}") for d in Days]
    flew       = [Bool(f"flew_{d}") for d in Days]

    s = Solver()

    # Domain constraints
    for d in Days:
        s.add(And(start_city[d-1] >= 0, start_city[d-1] < C))
        s.add(And(end_city[d-1]   >= 0, end_city[d-1]   < C))

    # Continuity constraints
    for d in Days:
        if d > 1:
            s.add(start_city[d-1] == end_city[d-2])

    # Flight constraints
    # If flew[d], then start != end and the pair must be in edges; else start == end
    # Build adjacency as a quick membership check
    allowed = {(a, b): True for (a, b) in edges}

    for d in Days:
        sd = start_city[d-1]
        ed = end_city[d-1]
        s.add(If(flew[d-1],
                 And(sd != ed,
                     Or([And(sd == a, ed == b) for (a, b) in edges])),
                 sd == ed))

    # Presence per day per city
    # presence[d][c] in {0,1}
    presence = [[Int(f"pres_d{d}_c{c}") for c in range(C)] for d in Days]
    for d in Days:
        sd = start_city[d-1]
        ed = end_city[d-1]
        for c in range(C):
            # presence is 1 if (flew and start==c) or end==c; but start==end when not flew
            s.add(presence[d-1][c] == If(flew[d-1],
                                         If(sd == c, 1, 0) + If(ed == c, 1, 0) - 0,  # start != end guaranteed when flew
                                         If(ed == c, 1, 0)))
            # However, because start != end when flew, sum is at most 2; but presence should be 1 max per city per day
            # Ensure 0/1 bounds
            s.add(Or(presence[d-1][c] == 0, presence[d-1][c] == 1))

    # Required total days per city
    required_days = {
        "Prague": 5,
        "Brussels": 2,
        "Riga": 2,
        "Munich": 2,
        "Seville": 3,
        "Stockholm": 2,
        "Istanbul": 2,
        "Amsterdam": 3,
        "Vienna": 5,
        "Split": 3,
    }

    for name, req in required_days.items():
        c = idx[name]
        s.add(Sum([presence[d-1][c] for d in Days]) == req)

    # Day-specific presence constraints

    # Prague: days 5-9 inclusive, and only those days
    prague = idx["Prague"]
    for d in Days:
        if 5 <= d <= 9:
            s.add(presence[d-1][prague] == 1)
        else:
            s.add(presence[d-1][prague] == 0)

    # Split: days 11-13 inclusive, and only those days
    split = idx["Split"]
    for d in Days:
        if 11 <= d <= 13:
            s.add(presence[d-1][split] == 1)
        else:
            s.add(presence[d-1][split] == 0)

    # Stockholm: days 16-17 inclusive, and only those days
    stockholm = idx["Stockholm"]
    for d in Days:
        if 16 <= d <= 17:
            s.add(presence[d-1][stockholm] == 1)
        else:
            s.add(presence[d-1][stockholm] == 0)

    # Riga: meet friends between day 15 and 16 -> be in Riga on both day 15 and day 16
    riga = idx["Riga"]
    for d in Days:
        if d in (15, 16):
            s.add(presence[d-1][riga] == 1)
        else:
            s.add(presence[d-1][riga] == 0)

    # Vienna: meet a friend in Vienna between day 1 and 5 (at least one of these days includes Vienna)
    vienna = idx["Vienna"]
    s.add(Sum([presence[d-1][vienna] for d in range(1, 6)]) >= 1)

    # Ensure the day 16 includes both Riga and Stockholm (already enforced by presence reqs)
    # This implicitly forces a flight on day 16 between Riga and Stockholm.
    # No explicit constraint needed beyond presence and flight semantics, but we can add a helper:
    d = 16
    s.add(flew[d-1] == True)
    s.add(Or(And(start_city[d-1] == riga, end_city[d-1] == stockholm),
             And(start_city[d-1] == stockholm, end_city[d-1] == riga)))

    # Ensure Split window requires entering on or before day 11 and leaving on or after day 13 due to presence constraints.
    # Already enforced by presence and continuity.

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found with given constraints."}))
        return

    m = s.model()

    # Build itinerary: for each day, list places present (start city if flew, and end city)
    itinerary = []
    for d in Days:
        sd = m[start_city[d-1]].as_long()
        ed = m[end_city[d-1]].as_long()
        fl = is_true(m[flew[d-1]])
        places = []
        if fl:
            # include both start and end
            places = [cities[sd], cities[ed]]
        else:
            places = [cities[ed]]
        itinerary.append({
            "day": f"Day {d}",
            "places": places
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
import json
from z3 import *

def main():
    # Define cities and indices
    cities = [
        "Brussels",
        "Helsinki",
        "Split",
        "Dubrovnik",
        "Istanbul",
        "Milan",
        "Vilnius",
        "Frankfurt",
    ]
    idx = {name: i for i, name in enumerate(cities)}
    n_days = 22

    # Desired presence days per city (including flight-day double-counting)
    desired_days = {
        "Brussels": 3,
        "Helsinki": 3,
        "Split": 4,
        "Dubrovnik": 2,
        "Istanbul": 5,
        "Milan": 4,
        "Vilnius": 5,
        "Frankfurt": 3,
    }

    # Directed flight edges: "A and B" => both directions; "from A to B" => only A->B
    edges = set()
    def add_ud(a, b):
        edges.add((idx[a], idx[b]))
        edges.add((idx[b], idx[a]))
    def add_dir(a, b):
        edges.add((idx[a], idx[b]))

    add_ud("Milan", "Frankfurt")
    add_ud("Split", "Frankfurt")
    add_ud("Milan", "Split")
    add_ud("Brussels", "Vilnius")
    add_ud("Brussels", "Helsinki")
    add_ud("Istanbul", "Brussels")
    add_ud("Milan", "Vilnius")
    add_ud("Brussels", "Milan")
    add_ud("Istanbul", "Helsinki")
    add_ud("Helsinki", "Vilnius")
    add_ud("Helsinki", "Dubrovnik")
    add_ud("Split", "Vilnius")
    add_dir("Dubrovnik", "Istanbul")
    add_ud("Istanbul", "Milan")
    add_ud("Helsinki", "Frankfurt")
    add_ud("Istanbul", "Vilnius")
    add_ud("Split", "Helsinki")
    add_ud("Milan", "Helsinki")
    add_ud("Istanbul", "Frankfurt")
    add_dir("Brussels", "Frankfurt")
    add_ud("Dubrovnik", "Frankfurt")
    add_ud("Frankfurt", "Vilnius")

    # Z3 variables: city per day (1-based indexing for clarity)
    c = [None] + [Int(f"c_{d}") for d in range(1, n_days + 1)]

    s = Solver()

    # Domain constraints
    for d in range(1, n_days + 1):
        s.add(And(c[d] >= 0, c[d] < len(cities)))

    # Enforce travel only on direct flights (at most one flight per day between end of day d and start of day d+1)
    # If c[d] != c[d+1], then (c[d], c[d+1]) must be an allowed directed edge
    allowed_pairs = list(edges)
    for d in range(1, n_days):
        s.add(Or(
            c[d] == c[d+1],
            Or(*[And(c[d] == a, c[d+1] == b) for (a, b) in allowed_pairs])
        ))

    # Presence booleans: present[city][day]
    present = {
        city: [None] + [Bool(f"present_{city}_{d}") for d in range(1, n_days + 1)]
        for city in cities
    }

    # Define presence: present(city, d) iff (c[d]==city) OR (flight on day d into city)
    # Flight on day d into city occurs when d < n_days and c[d] != c[d+1] and c[d+1] == city
    for city in cities:
        city_id = idx[city]
        for d in range(1, n_days + 1):
            if d < n_days:
                s.add(present[city][d] == Or(c[d] == city_id, And(c[d] != c[d+1], c[d+1] == city_id)))
            else:
                s.add(present[city][d] == (c[d] == city_id))

    # Desired total presence per city
    for city in cities:
        total = Sum([If(present[city][d], 1, 0) for d in range(1, n_days + 1)])
        s.add(total == desired_days[city])

    # Must attend Istanbul show on days 1-5 (present in Istanbul on each of these days)
    for d in range(1, 6):
        s.add(present["Istanbul"][d])

    # Attend Frankfurt wedding between day 16 and 18 (present in Frankfurt on each of these days)
    for d in range(16, 19):
        s.add(present["Frankfurt"][d])

    # Attend Vilnius workshop between day 18 and 22 (present in Vilnius on each of these days)
    for d in range(18, 23):
        s.add(present["Vilnius"][d])

    # It's natural to start in Istanbul on Day 1 for the show
    s.add(c[1] == idx["Istanbul"])

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found with given constraints."}))
        return

    m = s.model()
    day_cities = [None] + [m.evaluate(c[d]).as_long() for d in range(1, n_days + 1)]

    # Build merged itinerary runs by city-of-day with overlapping day boundaries on flight days
    runs = []
    start = 1
    for d in range(1, n_days):
        if day_cities[d] != day_cities[d + 1]:
            runs.append((start, d, day_cities[d]))
            start = d + 1
    runs.append((start, n_days, day_cities[n_days]))

    # Convert runs to desired output with overlapping day ranges:
    # For each run after the first, start day is shifted back by 1 to include the arrival day (flight day)
    itinerary = []
    for i, (sday, eday, city_id) in enumerate(runs):
        out_start = sday if i == 0 else sday - 1
        itinerary.append({
            "day_range": f"Day {out_start}-{eday}",
            "place": cities[city_id]
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
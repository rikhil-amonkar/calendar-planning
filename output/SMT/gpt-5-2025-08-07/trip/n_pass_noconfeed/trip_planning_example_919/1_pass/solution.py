import json
from z3 import *

def main():
    # Define cities
    cities = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]
    city_index = {name: i for i, name in enumerate(cities)}
    n_cities = len(cities)
    days = list(range(15))  # 0..14 correspond to Day 1..15

    # Required exact days in each city
    required_days = {
        "Vienna": 4,
        "Milan": 2,
        "Rome": 3,
        "Riga": 2,
        "Lisbon": 3,
        "Vilnius": 4,
        "Oslo": 3,
    }

    # Build allowed directed edges (start -> end)
    edges = set()
    def add_bidir(a, b):
        edges.add((city_index[a], city_index[b]))
        edges.add((city_index[b], city_index[a]))
    def add_dir(a, b):
        edges.add((city_index[a], city_index[b]))

    add_bidir("Riga", "Oslo")
    add_bidir("Rome", "Oslo")
    add_bidir("Vienna", "Milan")
    add_bidir("Vienna", "Vilnius")
    add_bidir("Vienna", "Lisbon")
    add_bidir("Riga", "Milan")
    add_bidir("Lisbon", "Oslo")
    add_dir("Rome", "Riga")
    add_bidir("Rome", "Lisbon")
    add_bidir("Vienna", "Riga")
    add_bidir("Vienna", "Rome")
    add_bidir("Milan", "Oslo")
    add_bidir("Vienna", "Oslo")
    add_bidir("Vilnius", "Oslo")
    add_dir("Riga", "Vilnius")
    add_bidir("Vilnius", "Milan")
    add_bidir("Riga", "Lisbon")
    add_bidir("Milan", "Lisbon")

    # Z3 variables
    Start = [Int(f"start_{d+1}") for d in days]  # city index at start of day
    End   = [Int(f"end_{d+1}") for d in days]    # city index at end of day
    Fly   = [Bool(f"fly_{d+1}") for d in days]   # whether we fly on day d+1

    s = Solver()

    # Domain constraints
    for d in days:
        s.add(And(Start[d] >= 0, Start[d] < n_cities))
        s.add(And(End[d] >= 0, End[d] < n_cities))
        # Fly[d] iff Start != End
        s.add(Fly[d] == (Start[d] != End[d]))

    # Continuity: next day's start is today's end
    for d in range(1, len(days)):
        s.add(Start[d] == End[d-1])

    # Movement constraints: either no flight (End == Start) or flight along an allowed edge
    for d in days:
        allowed_moves = [And(Start[d] == a, End[d] == b) for (a, b) in edges]
        s.add(Or(End[d] == Start[d], Or(allowed_moves)))

    # Presence helper
    def presence(day_idx, city_idx):
        return Or(Start[day_idx] == city_idx, End[day_idx] == city_idx)

    # Exact day counts per city
    for cname, req in required_days.items():
        cidx = city_index[cname]
        s.add(Sum([If(presence(d, cidx), 1, 0) for d in days]) == req)

    # Total flights equals sum(required_days) - total_days due to double-count on flight days
    total_required_city_days = sum(required_days.values())
    total_days = len(days)
    flights_required = total_required_city_days - total_days
    s.add(Sum([If(Fly[d], 1, 0) for d in days]) == flights_required)

    # Special constraints:
    # Day 1 and Day 4 must include Vienna (conference)
    s.add(presence(0, city_index["Vienna"]))  # Day 1
    s.add(presence(3, city_index["Vienna"]))  # Day 4

    # Lisbon between Day 11 and Day 13 inclusive (presence each day)
    for d in [10, 11, 12]:  # Days 11,12,13 -> indices 10,11,12
        s.add(presence(d, city_index["Lisbon"]) == True)

    # Oslo between Day 13 and Day 15 inclusive (presence each day)
    for d in [12, 13, 14]:  # Days 13,14,15 -> indices 12,13,14
        s.add(presence(d, city_index["Oslo"]) == True)

    # Solve
    if s.check() != sat:
        result = {"itinerary": []}
        print(json.dumps(result, ensure_ascii=False))
        return

    m = s.model()

    # Extract end-of-day cities and build itinerary ranges
    end_cities = [m.evaluate(End[d]).as_long() for d in days]
    # Aggregate consecutive same end-city into day ranges
    itinerary = []
    start_day = 1
    current_city = end_cities[0]
    for i in range(1, len(end_cities)):
        if end_cities[i] != current_city:
            itinerary.append({
                "day_range": f"Day {start_day}-{i}",
                "place": cities[current_city]
            })
            start_day = i + 1
            current_city = end_cities[i]
    # Append final range
    itinerary.append({
        "day_range": f"Day {start_day}-{len(days)}",
        "place": cities[current_city]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
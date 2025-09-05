import json
from z3 import *

def main():
    # Define constants
    D = 16  # total days

    # Cities and indices
    cities = ["Porto", "Prague", "Reykjavik", "Santorini", "Amsterdam", "Munich"]
    PORTO, PRAGUE, REYKJAVIK, SANTORINI, AMSTERDAM, MUNICH = range(6)

    # Direct flight edges (undirected)
    direct_pairs = [
        (PORTO, AMSTERDAM),
        (MUNICH, AMSTERDAM),
        (REYKJAVIK, AMSTERDAM),
        (MUNICH, PORTO),
        (PRAGUE, REYKJAVIK),
        (REYKJAVIK, MUNICH),
        (AMSTERDAM, SANTORINI),
        (PRAGUE, AMSTERDAM),
        (PRAGUE, MUNICH),
    ]
    # Make adjacency set symmetric
    adj = set()
    for a, b in direct_pairs:
        adj.add((a, b))
        adj.add((b, a))

    def is_adj(a, b):
        return Or([And(a == IntVal(x), b == IntVal(y)) for (x, y) in adj])

    # Z3 variables
    Start = [None] + [Int(f"Start_{d}") for d in range(1, D + 1)]
    End = [None] + [Int(f"End_{d}") for d in range(1, D + 1)]

    s = Solver()

    # Domain constraints
    for d in range(1, D + 1):
        s.add(And(Start[d] >= 0, Start[d] < len(cities)))
        s.add(And(End[d] >= 0, End[d] < len(cities)))

    # Continuity: you start day d where you ended day d-1
    for d in range(2, D + 1):
        s.add(Start[d] == End[d - 1])

    # Flight constraints: if Start != End, must be a direct flight
    for d in range(1, D + 1):
        s.add(Implies(Start[d] != End[d], is_adj(Start[d], End[d])))

    # Helper: whether a day includes a city (counts towards its stay)
    def includes_city(day, city):
        return Or(End[day] == city, And(Start[day] == city, Start[day] != End[day]))

    # Duration requirements
    required_days = {
        PORTO: 5,
        PRAGUE: 4,
        REYKJAVIK: 4,
        SANTORINI: 2,
        AMSTERDAM: 2,
        MUNICH: 4,
    }

    for c in range(len(cities)):
        s.add(Sum([If(includes_city(d, c), 1, 0) for d in range(1, D + 1)]) == required_days[c])

    # Total flights must match implied overcount: sum(required) = 21, so flights = 5
    s.add(Sum([If(Start[d] != End[d], 1, 0) for d in range(1, D + 1)]) == 5)

    # Constraints for attending events
    # Conference in Amsterdam on day 14 and 15
    s.add(includes_city(14, AMSTERDAM))
    s.add(includes_city(15, AMSTERDAM))

    # Wedding in Reykjavik between day 4 and 7 (inclusive): be in Reykjavik at least one of those days
    s.add(Or([includes_city(d, REYKJAVIK) for d in range(4, 8)]))

    # Meet friend in Munich between day 7 and 10 (inclusive): be in Munich at least one of those days
    s.add(Or([includes_city(d, MUNICH) for d in range(7, 11)]))

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found with given constraints"}))
        return

    m = s.model()

    # Extract End cities per day
    end_cities = [None] + [m.evaluate(End[d]).as_long() for d in range(1, D + 1)]
    start_cities = [None] + [m.evaluate(Start[d]).as_long() for d in range(1, D + 1)]

    # Build itinerary segments with overlap on flight days:
    # If End changes on day d (End[d] != End[d-1]), we close previous segment at d (inclusive)
    # and start new segment at d (inclusive), creating overlap on that day.
    segments = []
    seg_start = 1
    seg_city = end_cities[1]
    for d in range(2, D + 1):
        if end_cities[d] != end_cities[d - 1]:
            # Close previous segment at day d (inclusive)
            segments.append((seg_start, d, seg_city))
            # Start new segment at day d
            seg_start = d
            seg_city = end_cities[d]
    # Close last segment at D
    segments.append((seg_start, D, seg_city))

    # Convert to required JSON format
    itinerary = []
    for (a, b, cidx) in segments:
        itinerary.append({
            "day_range": f"Day {a}-{b}",
            "place": cities[cidx]
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
import json
from z3 import *

def main():
    # Define cities
    cities = ["Dublin", "Helsinki", "Riga", "Reykjavik", "Vienna", "Tallinn"]
    city_index = {name: i for i, name in enumerate(cities)}
    DUB, HEL, RIG, RKV, VIE, TAL = city_index["Dublin"], city_index["Helsinki"], city_index["Riga"], city_index["Reykjavik"], city_index["Vienna"], city_index["Tallinn"]

    # Required days per city (counted with rule: flight day counts for both origin and destination)
    required_days = {
        DUB: 5,
        HEL: 3,
        RIG: 3,
        RKV: 2,
        VIE: 2,
        TAL: 5,
    }

    total_days = 15

    # Direct flight availability (directed edges)
    # Pairs with "and" are bidirectional; "from Riga to Tallinn" is interpreted as directed Riga -> Tallinn
    allowed_edges = set()
    def add_bidirectional(a, b):
        allowed_edges.add((a, b))
        allowed_edges.add((b, a))

    add_bidirectional(HEL, RIG)        # Helsinki and Riga
    allowed_edges.add((RIG, TAL))      # from Riga to Tallinn
    add_bidirectional(VIE, HEL)        # Vienna and Helsinki
    add_bidirectional(RIG, DUB)        # Riga and Dublin
    add_bidirectional(VIE, RIG)        # Vienna and Riga
    add_bidirectional(RKV, VIE)        # Reykjavik and Vienna
    add_bidirectional(HEL, DUB)        # Helsinki and Dublin
    add_bidirectional(TAL, DUB)        # Tallinn and Dublin
    add_bidirectional(RKV, HEL)        # Reykjavik and Helsinki
    add_bidirectional(RKV, DUB)        # Reykjavik and Dublin
    add_bidirectional(HEL, TAL)        # Helsinki and Tallinn
    add_bidirectional(VIE, DUB)        # Vienna and Dublin

    # SMT variables
    s = Solver()
    c = [Int(f"c_{d}") for d in range(1, total_days + 1)]  # end-of-day city on day d
    flight = [Bool(f"flight_{d}") for d in range(1, total_days + 1)]  # whether a flight happens on day d

    # Domain constraints
    for d in range(total_days):
        s.add(And(c[d] >= 0, c[d] < len(cities)))

    # Flight and adjacency constraints
    s.add(flight[0] == False)  # No previous day for day 1
    for d in range(1, total_days):
        # flight[d] iff city changes between day d and day d+1 (0-indexed list, day number d+1)
        s.add(Implies(flight[d], c[d] != c[d-1]))
        s.add(Implies(c[d] != c[d-1], flight[d]))
        # If a flight occurs, it must be along an allowed directed edge
        # Start city is c[d-1], end city is c[d]
        s.add(Implies(flight[d], Or([And(c[d-1] == a, c[d] == b) for (a, b) in allowed_edges])))

    # Count presence in city per day
    def in_city_expr(city_idx, day_idx):
        # day_idx is 1-based for readability; our arrays are 0-based
        d = day_idx - 1
        current_city = (c[d] == city_idx)
        if day_idx == 1:
            # On day 1, there is no previous day; presence is only current city
            start_prev = False
        else:
            # If a flight occurs on this day, you're also present in the previous day's city
            start_prev = And(c[d-1] == city_idx, c[d] != c[d-1])
        return Or(current_city, start_prev)

    # City day count constraints
    for city_idx, req in required_days.items():
        s.add(Sum([If(in_city_expr(city_idx, d+1), 1, 0) for d in range(total_days)]) == req)

    # Total flights equals sum of (total city-day counts - total_days) = 20 - 15 = 5
    s.add(Sum([If(flight[d], 1, 0) for d in range(total_days)]) == 5)

    # Event constraints:
    # Annual show in Vienna on days 2 and 3
    s.add(in_city_expr(VIE, 2))
    s.add(in_city_expr(VIE, 3))
    # Meet friends in Helsinki between day 3 and day 5 (inclusive)
    s.add(Or(in_city_expr(HEL, 3), in_city_expr(HEL, 4), in_city_expr(HEL, 5)))
    # Attend a wedding in Tallinn between day 7 and day 11 (inclusive)
    s.add(Or(*[in_city_expr(TAL, d) for d in range(7, 12)]))

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": [], "status": "unsat"}))
        return
    m = s.model()

    # Extract end-of-day cities
    end_of_day_cities = [m.evaluate(c[d]).as_long() for d in range(total_days)]

    # Build consolidated day ranges by end-of-day city
    itinerary = []
    start = 1
    current_city = end_of_day_cities[0]
    for day in range(2, total_days + 1):
        if end_of_day_cities[day - 1] != current_city:
            itinerary.append({
                "day_range": f"Day {start}-{day - 1}",
                "place": cities[current_city]
            })
            start = day
            current_city = end_of_day_cities[day - 1]
    # Append the final range
    itinerary.append({
        "day_range": f"Day {start}-{total_days}",
        "place": cities[current_city]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
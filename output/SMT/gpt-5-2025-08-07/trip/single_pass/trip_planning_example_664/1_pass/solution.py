from z3 import *
import json

def solve_itinerary():
    # Cities and indices
    cities = ["Tallinn", "Bucharest", "Seville", "Stockholm", "Munich", "Milan"]
    city_to_idx = {name: i for i, name in enumerate(cities)}
    idx_to_city = {i: name for i, name in enumerate(cities)}

    # Required total days per city (counting flight days for both origin and destination)
    required_days = {
        "Tallinn": 2,
        "Bucharest": 4,
        "Seville": 5,
        "Stockholm": 5,
        "Munich": 5,
        "Milan": 2,
    }

    # Direct flights (undirected)
    direct_pairs = [
        ("Milan", "Stockholm"),
        ("Munich", "Stockholm"),
        ("Bucharest", "Munich"),
        ("Munich", "Seville"),
        ("Stockholm", "Tallinn"),
        ("Munich", "Milan"),
        ("Munich", "Tallinn"),
        ("Seville", "Milan"),
    ]
    directed_edges = []
    for a, b in direct_pairs:
        directed_edges.append((city_to_idx[a], city_to_idx[b]))
        directed_edges.append((city_to_idx[b], city_to_idx[a]))

    DAYS = 18
    # Variables: city at end of each day (1..18)
    city_vars = [Int(f"city_{d+1}") for d in range(DAYS)]

    s = Solver()

    # Domain constraints
    for d in range(DAYS):
        s.add(And(city_vars[d] >= 0, city_vars[d] < len(cities)))

    # Adjacency and flight/stay constraints:
    # Either stay in same city from day d-1 to day d, or move along a direct flight
    for d in range(1, DAYS):
        stay = (city_vars[d] == city_vars[d-1])
        moves = [And(city_vars[d-1] == i, city_vars[d] == j) for (i, j) in directed_edges]
        s.add(Or(stay, Or(moves)))

    # Helper: presence in city c on day d (1-based d)
    # present(d, c) := in c at end of day d OR flew out of c on day d (origin day)
    def present_expr(day_1based, c_idx):
        if day_1based == 1:
            return city_vars[0] == c_idx
        else:
            d = day_1based - 1  # 0-based index for arrays
            # present if end-of-day city is c, or if this day is a flight and origin (previous day) was c
            return Or(
                city_vars[d] == c_idx,
                And(city_vars[d-1] == c_idx, city_vars[d] != city_vars[d-1])
            )

    # Enforce total presence days per city
    for cname, req in required_days.items():
        c_idx = city_to_idx[cname]
        total = Sum([If(present_expr(d+1, c_idx), 1, 0) for d in range(DAYS)])
        s.add(total == req)

    # Window constraints (presence requirements)
    # Bucharest between day 1 and day 4 (inclusive)
    for d in range(1, 5):
        s.add(present_expr(d, city_to_idx["Bucharest"]))

    # Munich between day 4 and day 8 (inclusive)
    for d in range(4, 9):
        s.add(present_expr(d, city_to_idx["Munich"]))

    # Seville between day 8 and day 12 (inclusive)
    for d in range(8, 13):
        s.add(present_expr(d, city_to_idx["Seville"]))

    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    m = s.model()

    # Build the JSON itinerary: one city per day (end-of-day city)
    itinerary = []
    for d in range(DAYS):
        city_idx = m[city_vars[d]].as_long()
        itinerary.append({"day": d + 1, "city": idx_to_city[city_idx]})

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    solve_itinerary()
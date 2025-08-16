# Solve the 26-day, 10-city itinerary with flight-day double counting using Z3
# and output a JSON-formatted dictionary with day->city mapping.

import json
from z3 import *

def solve_itinerary():
    # Cities and indices
    cities = [
        "Prague",     # 0
        "Warsaw",     # 1
        "Dublin",     # 2
        "Athens",     # 3
        "Vilnius",    # 4
        "Porto",      # 5
        "London",     # 6
        "Seville",    # 7
        "Lisbon",     # 8
        "Dubrovnik"   # 9
    ]
    city_index = {name: i for i, name in enumerate(cities)}
    n_days = 26
    n_cities = len(cities)

    # Required "stay" counts per city (with flight-day double counting)
    required_days = {
        "Prague": 3,
        "Warsaw": 4,
        "Dublin": 3,
        "Athens": 3,
        "Vilnius": 4,
        "Porto": 5,
        "London": 3,
        "Seville": 2,
        "Lisbon": 5,
        "Dubrovnik": 3,
    }

    # Direct flights (undirected)
    direct_pairs = [
        ("Warsaw", "Vilnius"),
        ("Prague", "Athens"),
        ("London", "Lisbon"),
        ("Lisbon", "Porto"),
        ("Prague", "Lisbon"),
        ("London", "Dublin"),
        ("Athens", "Vilnius"),
        ("Athens", "Dublin"),
        ("Prague", "London"),
        ("London", "Warsaw"),
        ("Dublin", "Seville"),
        ("Seville", "Porto"),
        ("Lisbon", "Athens"),
        ("Dublin", "Porto"),
        ("Athens", "Warsaw"),
        ("Lisbon", "Warsaw"),
        ("Porto", "Warsaw"),
        ("Prague", "Warsaw"),
        ("Prague", "Dublin"),
        ("Athens", "Dubrovnik"),
        ("Lisbon", "Dublin"),
        ("Dubrovnik", "Dublin"),
        ("Lisbon", "Seville"),
        ("London", "Athens"),
    ]
    # Build adjacency matrix
    allowed = [[False]*n_cities for _ in range(n_cities)]
    for a, b in direct_pairs:
        i, j = city_index[a], city_index[b]
        allowed[i][j] = True
        allowed[j][i] = True

    # Z3 variables
    # city[d]: city index at the end of day d (1-based days)
    city = {d: Int(f"city_{d}") for d in range(1, n_days+1)}
    # ch[d]: True iff there is a flight on day d (i.e., city[d] != city[d-1]), for d in 2..n_days
    ch = {d: Bool(f"ch_{d}") for d in range(2, n_days+1)}

    s = Solver()

    # Domain constraints for city variables
    for d in range(1, n_days+1):
        s.add(And(city[d] >= 0, city[d] < n_cities))

    # Link change variables ch[d] with city changes and enforce direct flights on change days
    for d in range(2, n_days+1):
        # ch[d] <-> city[d] != city[d-1]
        s.add(Implies(ch[d], city[d] != city[d-1]))
        s.add(Implies(Not(ch[d]), city[d] == city[d-1]))

        # If there is a change, it must be along an allowed direct flight
        # For all i != j where not allowed[i][j], we cannot have (ch[d] and city[d-1]==i and city[d]==j)
        for i in range(n_cities):
            for j in range(n_cities):
                if i != j and not allowed[i][j]:
                    s.add(Not(And(ch[d], city[d-1] == i, city[d] == j)))

    # Helper to build "in city on day t" expression (flight day counts for both origin and destination)
    def in_city_on_day_expr(c_idx, t):
        if t == 1:
            return city[1] == c_idx
        else:
            return Or(city[t] == c_idx, And(ch[t] == True, city[t-1] == c_idx))

    # Duration constraints with flight-day double counting
    for name, req in required_days.items():
        idx = city_index[name]
        count_terms = []
        for t in range(1, n_days+1):
            count_terms.append(If(in_city_on_day_expr(idx, t), 1, 0))
        s.add(Sum(count_terms) == req)

    # Sum of changes equals total overlap needed: sum(required) - n_days = 35 - 26 = 9
    total_required = sum(required_days.values())
    required_changes = total_required - n_days
    s.add(Sum([If(ch[d], 1, 0) for d in range(2, n_days+1)]) == required_changes)

    # Windowed presence constraints (must be in those cities on those days, counting flight overlap)
    def enforce_presence(city_name, start_day, end_day):
        c_idx = city_index[city_name]
        for t in range(start_day, end_day+1):
            s.add(in_city_on_day_expr(c_idx, t))

    # Constraints from problem text:
    # Prague workshop between day 1 and day 3
    enforce_presence("Prague", 1, 3)
    # London wedding between day 3 and day 5
    enforce_presence("London", 3, 5)
    # Lisbon relatives between day 5 and day 9
    enforce_presence("Lisbon", 5, 9)
    # Porto conference during day 16 and day 20
    enforce_presence("Porto", 16, 20)
    # Warsaw friends between day 20 and day 23
    enforce_presence("Warsaw", 20, 23)

    # Solve
    if s.check() != sat:
        raise RuntimeError("No valid itinerary found.")
    m = s.model()

    # Build itinerary: map each day to the city at end of day (JSON expects a single city per day)
    itinerary = []
    for d in range(1, n_days+1):
        c_idx = m[city[d]].as_long()
        itinerary.append({"day": d, "city": cities[c_idx]})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))
from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = [
        "Prague",    # 0
        "Tallinn",   # 1
        "Warsaw",    # 2
        "Porto",     # 3
        "Naples",    # 4
        "Milan",     # 5
        "Lisbon",    # 6
        "Santorini", # 7
        "Riga",      # 8
        "Stockholm"  # 9
    ]
    city_index = {c: i for i, c in enumerate(cities)}
    n_days = 28

    # Required days "in" each city (counting flight overlap as per rules)
    required = {
        "Prague": 5,
        "Tallinn": 3,
        "Warsaw": 2,
        "Porto": 3,
        "Naples": 5,
        "Milan": 3,
        "Lisbon": 5,
        "Santorini": 5,
        "Riga": 4,
        "Stockholm": 2
    }

    # Build directed adjacency according to problem statement
    allowed_edges = []
    def add_bi(a, b):
        allowed_edges.append((city_index[a], city_index[b]))
        allowed_edges.append((city_index[b], city_index[a]))
    def add_dir(a, b):
        allowed_edges.append((city_index[a], city_index[b]))

    add_bi("Riga", "Prague")
    add_bi("Stockholm", "Milan")
    add_bi("Riga", "Milan")
    add_bi("Lisbon", "Stockholm")
    add_dir("Stockholm", "Santorini")  # directed
    add_bi("Naples", "Warsaw")
    add_bi("Lisbon", "Warsaw")
    add_bi("Naples", "Milan")
    add_bi("Lisbon", "Naples")
    add_dir("Riga", "Tallinn")         # directed
    add_bi("Tallinn", "Prague")
    add_bi("Stockholm", "Warsaw")
    add_bi("Riga", "Warsaw")
    add_bi("Lisbon", "Riga")
    add_bi("Riga", "Stockholm")
    add_bi("Lisbon", "Porto")
    add_bi("Lisbon", "Prague")
    add_bi("Milan", "Porto")
    add_bi("Prague", "Milan")
    add_bi("Lisbon", "Milan")
    add_bi("Warsaw", "Porto")
    add_bi("Warsaw", "Tallinn")
    add_bi("Santorini", "Milan")
    add_bi("Stockholm", "Prague")
    add_bi("Stockholm", "Tallinn")
    add_bi("Warsaw", "Milan")
    add_bi("Santorini", "Naples")
    add_bi("Warsaw", "Prague")

    # Z3 setup
    City = [Int(f"City_{d}") for d in range(1, n_days + 1)]
    s = Solver()

    # Domain constraints
    for d in range(n_days):
        s.add(And(City[d] >= 0, City[d] < len(cities)))

    # Changes and adjacency constraints
    # For each day d>=2, if City[d] != City[d-1], it must be an allowed edge
    for d in range(1, n_days):  # 0-based index; day 2..28
        prev = City[d - 1]
        curr = City[d]
        # Build disjunction of allowed pairs
        allowed_pair = Or(*[And(prev == i, curr == j) for (i, j) in allowed_edges])
        s.add(Or(curr == prev, allowed_pair))

    # Helper expressions
    def eq_city(expr, c):
        return If(expr == c, 1, 0)

    # change[d] for d>=2: 1 if City[d] != City[d-1], else 0
    change = [IntVal(0)] * n_days
    for d in range(1, n_days):
        change[d] = If(City[d] != City[d - 1], 1, 0)

    # Count per city: sum of days with City[d]==c plus sum of departure days where previous day equals c and change occurs
    counts = [Int(f"count_{c}") for c in range(len(cities))]
    for c in range(len(cities)):
        sum_eq = Sum([eq_city(City[d], c) for d in range(n_days)])
        sum_dep = Sum([If(And(City[d - 1] == c, City[d] != City[d - 1]), 1, 0) for d in range(1, n_days)])
        s.add(counts[c] == sum_eq + sum_dep)

    # Total transitions must be 9 (10 city segments, matching 10 cities)
    s.add(Sum(change) == 9)

    # Required days in each city
    for name, req in required.items():
        s.add(counts[city_index[name]] == req)

    # "In city on day d" indicator: 1 if City[d]==c, or (d>=2 and change on day d and City[d-1]==c)
    def in_city_on_day(d, c):
        if d == 0:
            # day 1: only City[0] == c counts
            return eq_city(City[0], c)
        else:
            return If(Or(City[d] == c, And(City[d - 1] == c, City[d] != City[d - 1])), 1, 0)

    # Riga show on days 5-8 (days are 1-indexed; convert to 0-index in code)
    riga = city_index["Riga"]
    for day in range(5, 9):
        s.add(in_city_on_day(day - 1, riga) == 1)

    # Tallinn relatives on days 18-20
    tallinn = city_index["Tallinn"]
    for day in range(18, 21):
        s.add(in_city_on_day(day - 1, tallinn) == 1)

    # Milan friend between day 24 and day 26 (at least one of these days "in" Milan)
    milan = city_index["Milan"]
    s.add(Sum([in_city_on_day(day - 1, milan) for day in range(24, 27)]) >= 1)

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found.")

    m = s.model()
    itinerary = []
    for d in range(n_days):
        city = cities[m[City[d]].as_long()]
        itinerary.append({"day": d + 1, "city": city})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))
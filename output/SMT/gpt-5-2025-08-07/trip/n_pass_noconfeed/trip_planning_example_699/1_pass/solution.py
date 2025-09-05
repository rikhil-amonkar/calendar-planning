import json
from z3 import Solver, Int, Or, And, If, Sum, sat

def main():
    # Cities and indices
    cities = ["Hamburg", "Dublin", "Helsinki", "Reykjavik", "London", "Mykonos"]
    city_idx = {name: i for i, name in enumerate(cities)}

    D = 16  # total days (1..16)

    # Direct flight pairs (undirected)
    direct_pairs = [
        ("Dublin", "London"),
        ("Hamburg", "Dublin"),
        ("Helsinki", "Reykjavik"),
        ("Hamburg", "London"),
        ("Dublin", "Helsinki"),
        ("Reykjavik", "London"),
        ("London", "Mykonos"),
        ("Dublin", "Reykjavik"),
        ("Hamburg", "Helsinki"),
        ("Helsinki", "London"),
    ]
    direct = set()
    for a, b in direct_pairs:
        direct.add((city_idx[a], city_idx[b]))
        direct.add((city_idx[b], city_idx[a]))

    # Required days in each city
    required_days = {
        "Mykonos": 3,
        "Reykjavik": 2,
        "Dublin": 5,
        "London": 5,
        "Helsinki": 4,
        "Hamburg": 2,
    }

    # Create Z3 variables: L[0..D], where L[d] is the city at the end of day d (L[0] is "day 0" start city)
    L = [Int(f"L_{d}") for d in range(D + 1)]

    s = Solver()

    # Domain constraints
    for d in range(D + 1):
        s.add(Or([L[d] == i for i in range(len(cities))]))

    # Direct flight or stay constraint per day
    for d in range(1, D + 1):
        # Either stay in same city, or make a single direct flight to a connected city
        conds = [L[d] == L[d - 1]]
        # Enumerate all allowable direct transitions (i -> j)
        for (i, j) in direct:
            conds.append(And(L[d - 1] == i, L[d] == j))
        s.add(Or(conds))

    # Presence helper (you are in a city on day d if either L[d-1] or L[d] equals that city)
    def present(day, cidx):
        return Or(L[day - 1] == cidx, L[day] == cidx)

    # Duration constraints (exact days present in each city)
    for cname, req in required_days.items():
        cidx = city_idx[cname]
        s.add(Sum([If(present(d, cidx), 1, 0) for d in range(1, D + 1)]) == req)

    # Special constraints:
    # - Hamburg friends between day 1 and day 2 (be present both days)
    s.add(present(1, city_idx["Hamburg"]))
    s.add(present(2, city_idx["Hamburg"]))

    # - Dublin show between day 2 and day 6 inclusive (present every day)
    for d in range(2, 7):
        s.add(present(d, city_idx["Dublin"]))

    # - Reykjavik wedding between day 9 and day 10 (present both days)
    s.add(present(9, city_idx["Reykjavik"]))
    s.add(present(10, city_idx["Reykjavik"]))

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = s.model()

    # Build per-day presence labels (one or two cities per day; sort for consistency)
    day_labels = []
    for d in range(1, D + 1):
        present_cities = []
        for cname, idx in city_idx.items():
            val = m.eval(present(d, idx), model_completion=True)
            if str(val) == "True":
                present_cities.append(cname)
        present_cities_sorted = sorted(present_cities)
        label = " & ".join(present_cities_sorted)
        day_labels.append(label)

    # Compress consecutive days with identical labels into ranges
    itinerary = []
    start = 1
    current_label = day_labels[0]
    for day in range(2, D + 1):
        if day_labels[day - 1] != current_label:
            itinerary.append({"day_range": f"Day {start}-{day-1}", "place": current_label})
            start = day
            current_label = day_labels[day - 1]
    # Append last range
    itinerary.append({"day_range": f"Day {start}-{D}", "place": current_label})

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()
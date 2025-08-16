from z3 import *
import json

def solve_itinerary():
    # Problem data
    days = 12
    cities = ["Split", "Helsinki", "Reykjavik", "Vilnius", "Geneva"]
    city_index = {name: i for i, name in enumerate(cities)}

    required_days = {
        "Split": 2,
        "Helsinki": 2,
        "Reykjavik": 3,
        "Vilnius": 3,
        "Geneva": 6,
    }

    # Undirected edges (direct flights)
    undirected_edges = [
        ("Split", "Helsinki"),
        ("Geneva", "Split"),
        ("Geneva", "Helsinki"),
        ("Helsinki", "Reykjavik"),
        ("Vilnius", "Helsinki"),
        ("Split", "Vilnius"),
    ]
    # Build directed adjacency set
    directed_edges = set()
    for a, b in undirected_edges:
        directed_edges.add((city_index[a], city_index[b]))
        directed_edges.add((city_index[b], city_index[a]))

    # Z3 variables: city per day (0..len(cities)-1)
    city = [Int(f"city_{d+1}") for d in range(days)]

    s = Solver()

    # Domain constraints
    for d in range(days):
        s.add(And(city[d] >= 0, city[d] < len(cities)))

    # Adjacency constraints: if city changes from day d to d+1, must be a direct flight
    for d in range(1, days):
        # allowed if same city or in directed_edges
        allowed_pairs = [And(city[d-1] == a, city[d] == b) for (a, b) in directed_edges]
        s.add(Or(city[d] == city[d-1], Or(*allowed_pairs)))

    # Count function components:
    # For each city c:
    # total(c) = assigned_days(c) + departures(c)
    # where departures(c) counts days d (2..days) with city[d-1]==c and city[d]!=c
    for cname, req in required_days.items():
        c = city_index[cname]
        assigned = Sum([If(city[d] == c, 1, 0) for d in range(days)])
        departures = Sum([If(And(city[d-1] == c, city[d] != c), 1, 0) for d in range(1, days)])
        s.add(assigned + departures == req)

    # Window constraints:
    # Reykjavik wedding between day 10 and day 12: be in Reykjavik on at least one of these days
    def in_city_on_day(ci, d_idx):
        # d_idx is 0-based index; day = d_idx+1
        if d_idx == 0:
            return city[0] == ci
        return Or(city[d_idx] == ci, And(city[d_idx - 1] == ci, city[d_idx] != ci))

    # Reykjavik presence in days 10..12 (indices 9..11)
    rkv = city_index["Reykjavik"]
    s.add(Sum([If(in_city_on_day(rkv, d), 1, 0) for d in range(9, 12)]) >= 1)

    # Vilnius relatives between day 7 and day 9: be in Vilnius on at least one of these days
    vno = city_index["Vilnius"]
    s.add(Sum([If(in_city_on_day(vno, d), 1, 0) for d in range(6, 9)]) >= 1)

    # Optional: enforce number of transitions equals sum(required_days)-days
    # Because each transition day counts for both cities
    total_required = sum(required_days.values())
    transitions_needed = total_required - days
    transitions = Sum([If(city[d] != city[d-1], 1, 0) for d in range(1, days)])
    s.add(transitions == transitions_needed)

    if s.check() != sat:
        print(json.dumps({"itinerary": []}, indent=2))
        return

    m = s.model()
    itinerary = []
    for d in range(days):
        cidx = m[city[d]].as_long()
        itinerary.append({"day": d + 1, "city": cities[cidx]})

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    solve_itinerary()
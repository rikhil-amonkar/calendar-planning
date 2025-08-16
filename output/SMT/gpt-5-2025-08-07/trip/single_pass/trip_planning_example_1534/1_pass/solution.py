# Requires: z3-solver
# pip install z3-solver
from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = [
        "Paris",
        "Venice",
        "Vilnius",
        "Salzburg",
        "Amsterdam",
        "Barcelona",
        "Hamburg",
        "Florence",
        "Warsaw",
        "Tallinn",
    ]
    idx = {c: i for i, c in enumerate(cities)}

    days = 25
    # Variables: city for each day (0-based index for days)
    City = [Int(f"city_{d}") for d in range(days)]

    s = Solver()

    # Domains
    for d in range(days):
        s.add(And(City[d] >= 0, City[d] < len(cities)))

    # Direct flights (edges)
    # Undirected helper
    def add_edge(edges, a, b):
        edges.add((idx[a], idx[b]))
        edges.add((idx[b], idx[a]))

    # Directed helper
    def add_edge_dir(edges, a, b):
        edges.add((idx[a], idx[b]))

    edges = set()
    add_edge(edges, "Paris", "Venice")
    add_edge(edges, "Barcelona", "Amsterdam")
    add_edge(edges, "Amsterdam", "Warsaw")
    add_edge(edges, "Amsterdam", "Vilnius")
    add_edge(edges, "Barcelona", "Warsaw")
    add_edge(edges, "Warsaw", "Venice")
    add_edge(edges, "Amsterdam", "Hamburg")
    add_edge(edges, "Barcelona", "Hamburg")
    add_edge(edges, "Barcelona", "Florence")
    add_edge(edges, "Barcelona", "Venice")
    add_edge(edges, "Paris", "Hamburg")
    add_edge(edges, "Paris", "Vilnius")
    add_edge(edges, "Paris", "Amsterdam")
    add_edge(edges, "Paris", "Florence")
    add_edge(edges, "Florence", "Amsterdam")
    add_edge(edges, "Vilnius", "Warsaw")
    add_edge(edges, "Barcelona", "Tallinn")
    add_edge(edges, "Paris", "Warsaw")
    add_edge(edges, "Tallinn", "Warsaw")
    add_edge_dir(edges, "Tallinn", "Vilnius")  # directed
    add_edge(edges, "Amsterdam", "Tallinn")
    add_edge(edges, "Paris", "Tallinn")
    add_edge(edges, "Paris", "Barcelona")
    add_edge(edges, "Venice", "Hamburg")
    add_edge(edges, "Warsaw", "Hamburg")
    add_edge(edges, "Hamburg", "Salzburg")
    add_edge(edges, "Amsterdam", "Venice")

    # Movement constraints: stay or direct flight if changing cities
    for d in range(days - 1):
        stay = City[d + 1] == City[d]
        direct = Or([And(City[d] == a, City[d + 1] == b) for (a, b) in edges])
        s.add(Or(stay, direct))

    # Presence function per day & city (captures flight-day double counting)
    # presence(d,c) := City[d] == c OR (d<last and City[d]!=City[d+1] and City[d+1]==c)
    def presence(d, c):
        if d < days - 1:
            return Or(City[d] == c, And(City[d] != City[d + 1], City[d + 1] == c))
        else:
            return City[d] == c

    # Required lengths per city (counting flight-day double presence)
    required = {
        "Warsaw": 4,
        "Venice": 3,
        "Vilnius": 3,
        "Salzburg": 4,
        "Amsterdam": 2,
        "Barcelona": 5,
        "Paris": 2,
        "Hamburg": 4,
        "Florence": 5,
        "Tallinn": 2,
    }

    for cname, req in required.items():
        c = idx[cname]
        s.add(Sum([If(presence(d, c), 1, 0) for d in range(days)]) == req)

    # Time-window constraints (presence on specific days)
    # Paris workshop: days 1-2 (index 0,1)
    for d in [0, 1]:
        s.add(presence(d, idx["Paris"]))

    # Barcelona tour with friends: days 2-6 (index 1..5)
    for d in range(1, 6):
        s.add(presence(d, idx["Barcelona"]))

    # Hamburg conference: days 19-22 (index 18..21)
    for d in range(18, 22):
        s.add(presence(d, idx["Hamburg"]))

    # Salzburg wedding: days 22-25 (index 21..24)
    for d in range(21, 25):
        s.add(presence(d, idx["Salzburg"]))

    # Tallinn friend meetup: days 11-12 (index 10..11)
    for d in [10, 11]:
        s.add(presence(d, idx["Tallinn"]))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found.")

    m = s.model()
    itinerary = []
    for d in range(days):
        cidx = m.eval(City[d]).as_long()
        itinerary.append({"day": d + 1, "city": cities[cidx]})

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))


if __name__ == "__main__":
    solve_itinerary()
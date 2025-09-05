import json
from z3 import *

def solve_itinerary():
    # Define cities
    cities = [
        "Paris", "Barcelona", "Florence", "Amsterdam",
        "Tallinn", "Vilnius", "Warsaw", "Venice",
        "Hamburg", "Salzburg"
    ]
    n = len(cities)

    # Durations per city (inclusive of flight days per problem statement)
    durations = {
        "Warsaw": 4,
        "Venice": 3,
        "Vilnius": 3,
        "Salzburg": 4,
        "Amsterdam": 2,
        "Barcelona": 5,
        "Paris": 2,
        "Hamburg": 4,
        "Florence": 5,
        "Tallinn": 2
    }

    # Flight adjacency (direct flights). "and" indicates bidirectional, "from A to B" indicates directed
    edges = set()
    def add_undirected(a, b):
        edges.add((a, b))
        edges.add((b, a))
    def add_directed(a, b):
        edges.add((a, b))

    add_undirected("Paris", "Venice")
    add_undirected("Barcelona", "Amsterdam")
    add_undirected("Amsterdam", "Warsaw")
    add_undirected("Amsterdam", "Vilnius")
    add_undirected("Barcelona", "Warsaw")
    add_undirected("Warsaw", "Venice")
    add_undirected("Amsterdam", "Hamburg")
    add_undirected("Barcelona", "Hamburg")
    add_undirected("Barcelona", "Florence")
    add_undirected("Barcelona", "Venice")
    add_undirected("Paris", "Hamburg")
    add_undirected("Paris", "Vilnius")
    add_undirected("Paris", "Amsterdam")
    add_undirected("Paris", "Florence")
    add_undirected("Florence", "Amsterdam")
    add_undirected("Vilnius", "Warsaw")
    add_undirected("Barcelona", "Tallinn")
    add_undirected("Paris", "Warsaw")
    add_undirected("Tallinn", "Warsaw")
    add_directed("Tallinn", "Vilnius")
    add_undirected("Amsterdam", "Tallinn")
    add_undirected("Paris", "Tallinn")
    add_undirected("Paris", "Barcelona")
    add_undirected("Venice", "Hamburg")
    add_undirected("Warsaw", "Hamburg")
    add_undirected("Hamburg", "Salzburg")
    add_undirected("Amsterdam", "Venice")

    def edge_allowed(a, b):
        return (a, b) in edges

    # Windows constraints (stay must be fully within the given window)
    # These windows reflect the "must be there between days X and Y" statements,
    # paired with the fixed duration to pin exact ranges when applicable.
    windows = {
        "Paris": (1, 2),      # 2 days; workshop between day 1 and day 2
        "Barcelona": (2, 6),  # 5 days; friends between day 2 and day 6
        "Hamburg": (19, 22),  # 4 days; conference during day 19-22
        "Salzburg": (22, 25), # 4 days; wedding between day 22 and day 25
        "Tallinn": (11, 12)   # 2 days; meet between day 11 and day 12
    }

    # Z3 variables
    s = {c: Int(f"s_{c}") for c in cities}   # start day (inclusive)
    e = {c: Int(f"e_{c}") for c in cities}   # end day (inclusive)
    pos = {c: Int(f"pos_{c}") for c in cities}  # order position in the itinerary

    solver = Solver()

    # Domains and duration constraints
    for c in cities:
        solver.add(s[c] >= 1, s[c] <= 25)
        solver.add(e[c] >= 1, e[c] <= 25)
        solver.add(e[c] >= s[c])
        solver.add(e[c] - s[c] + 1 == durations[c])
        solver.add(pos[c] >= 0, pos[c] < n)

    # All positions must be distinct (a permutation of 0..n-1)
    solver.add(Distinct([pos[c] for c in cities]))

    # Windows constraints
    for c, (lo, hi) in windows.items():
        solver.add(s[c] >= lo, e[c] <= hi)

    # The first city starts at day 1; the last city ends at day 25
    for c in cities:
        solver.add(Implies(pos[c] == 0, s[c] == 1))
        solver.add(Implies(pos[c] == n - 1, e[c] == 25))

    # Temporal alignment and flight constraints:
    # - Adjacent cities in the order share the boundary day: e[a] == s[b]
    # - Non-adjacent cities must be strictly separated: e[a] + 1 <= s[b]
    # - Adjacent cities must have a direct flight from a to b
    for a in cities:
        for b in cities:
            if a == b:
                continue
            # If b immediately follows a
            solver.add(Implies(pos[a] + 1 == pos[b], And(
                e[a] == s[b],
                BoolVal(edge_allowed(a, b))
            )))
            # If b comes after a but not immediately
            solver.add(Implies(pos[a] + 1 < pos[b], e[a] + 1 <= s[b]))

    # Solve
    if solver.check() != sat:
        raise RuntimeError("No valid itinerary found under given constraints.")

    model = solver.model()

    # Extract and order the itinerary
    itinerary_items = []
    for c in cities:
        itinerary_items.append({
            "city": c,
            "pos": model.eval(pos[c]).as_long(),
            "start": model.eval(s[c]).as_long(),
            "end": model.eval(e[c]).as_long()
        })
    itinerary_items.sort(key=lambda x: x["pos"])

    # Build JSON structure
    itinerary = []
    for item in itinerary_items:
        itinerary.append({
            "day_range": f"Day {item['start']}-{item['end']}",
            "place": item["city"]
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False))
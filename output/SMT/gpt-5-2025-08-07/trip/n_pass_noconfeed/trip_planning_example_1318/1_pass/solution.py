import json
from z3 import *

def main():
    # City indices
    cities = [
        "Oslo",       # 0
        "Helsinki",   # 1
        "Edinburgh",  # 2
        "Riga",       # 3
        "Tallinn",    # 4
        "Budapest",   # 5
        "Vilnius",    # 6
        "Porto",      # 7
        "Geneva"      # 8
    ]
    city_index = {name: i for i, name in enumerate(cities)}

    # Trip length
    D = 25
    days = range(1, D + 1)

    # Required presence days per city (these count flight overlap days as well)
    req = {
        "Oslo": 2,
        "Helsinki": 2,
        "Edinburgh": 3,
        "Riga": 2,
        "Tallinn": 5,
        "Budapest": 5,
        "Vilnius": 5,
        "Porto": 5,
        "Geneva": 4
    }

    # Directed edges (from, to). Undirected are added as both directions.
    directed_edges = set()
    undirected_pairs = []

    # Parse flight network from prompt
    # Undirected: "A and B"
    undirected_pairs += [
        ("Porto", "Oslo"),
        ("Edinburgh", "Budapest"),
        ("Edinburgh", "Geneva"),
        ("Edinburgh", "Porto"),
        ("Vilnius", "Helsinki"),
        ("Riga", "Oslo"),
        ("Geneva", "Oslo"),
        ("Edinburgh", "Oslo"),
        ("Edinburgh", "Helsinki"),
        ("Vilnius", "Oslo"),
        ("Riga", "Helsinki"),
        ("Budapest", "Geneva"),
        ("Helsinki", "Budapest"),
        ("Helsinki", "Oslo"),
        ("Edinburgh", "Riga"),
        ("Tallinn", "Helsinki"),
        ("Geneva", "Porto"),
        ("Budapest", "Oslo"),
        ("Helsinki", "Geneva"),
        ("Tallinn", "Oslo"),
    ]
    # Directed: "from A to B"
    directed_only = [
        ("Riga", "Tallinn"),
        ("Tallinn", "Vilnius"),
        ("Riga", "Vilnius"),
    ]

    # Build adjacency as directed pairs
    adjacency = set()
    for a, b in undirected_pairs:
        ai = city_index[a]
        bi = city_index[b]
        adjacency.add((ai, bi))
        adjacency.add((bi, ai))
    for a, b in directed_only:
        ai = city_index[a]
        bi = city_index[b]
        adjacency.add((ai, bi))

    # Z3 variables
    city = [Int(f"city_{d}") for d in range(0, D + 1)]  # city[0] is start reference
    flew = [Bool(f"flew_{d}") if d >= 1 else False for d in range(0, D + 1)]  # flew[0] unused

    s = Solver()

    # Domain constraints for cities
    for d in range(0, D + 1):
        s.add(And(city[d] >= 0, city[d] < len(cities)))

    # Movement and adjacency constraints
    for d in days:
        # If flew on day d, city changes and must be a direct flight from city[d-1] to city[d]
        if_flew_then_direct = Implies(
            flew[d],
            And(
                city[d] != city[d - 1],
                Or([And(city[d - 1] == i, city[d] == j) for (i, j) in adjacency])
            )
        )
        # If no flight, stay in same city
        if_not_flew_then_same = Implies(Not(flew[d]), city[d] == city[d - 1])
        s.add(if_flew_then_direct, if_not_flew_then_same)

    # Presence expression: presence[d][c] is True if on day d we are in city c
    def presence_expr(d, c):
        return Or(city[d] == c, And(flew[d], city[d - 1] == c))

    # Duration constraints
    for name, needed in req.items():
        c = city_index[name]
        present_count = Sum([If(presence_expr(d, c), 1, 0) for d in days])
        s.add(present_count == needed)

    # Total flights equals sum(req) - D (because each flight adds an extra city-day)
    total_required_days = sum(req.values())
    needed_flights = total_required_days - D
    flight_sum = Sum([If(flew[d], 1, 0) for d in days])
    s.add(flight_sum == needed_flights)

    # Meeting in Oslo on day 24 or 25
    OSL = city_index["Oslo"]
    s.add(Or(presence_expr(24, OSL), presence_expr(25, OSL)))

    # Wedding in Tallinn between day 4 and 8
    TLL = city_index["Tallinn"]
    s.add(Or(*[presence_expr(d, TLL) for d in range(4, 9)]))

    # Encourage clean segment itinerary:
    # - Do not fly on day 1 (start in a city without an immediate flight)
    s.add(Not(flew[1]))
    # - Appear in each city at least once as end-of-day city (helps readable itinerary)
    for c in range(len(cities)):
        s.add(Or(*[city[d] == c for d in days]))

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    m = s.model()

    # Extract end-of-day city sequence
    end_cities = [m[city[d]].as_long() for d in days]

    # Build non-overlapping itinerary by end-of-day segments
    itinerary = []
    start = 1
    current = end_cities[0]
    for idx, d in enumerate(range(2, D + 1), start=2):
        if end_cities[idx - 2] != end_cities[idx - 1]:
            end_day = d - 1
            itinerary.append({
                "day_range": f"Day {start}-{end_day}",
                "place": cities[current]
            })
            start = d
            current = end_cities[idx - 1]
    # Append last segment
    itinerary.append({
        "day_range": f"Day {start}-{D}",
        "place": cities[current]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
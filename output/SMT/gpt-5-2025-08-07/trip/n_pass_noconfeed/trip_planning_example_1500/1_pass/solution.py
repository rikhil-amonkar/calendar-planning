import json
from z3 import Optimize, Int, If, Or, And, Sum, Implies

def main():
    # Define cities and indices
    cities = [
        "London", "Milan", "Zurich", "Reykjavik",
        "Hamburg", "Barcelona", "Stuttgart", "Stockholm",
        "Tallinn", "Bucharest"
    ]
    idx = {name: i for i, name in enumerate(cities)}
    A_set = {idx["London"], idx["Milan"], idx["Zurich"], idx["Reykjavik"]}
    B_set = {idx["Hamburg"], idx["Barcelona"], idx["Stuttgart"], idx["Stockholm"], idx["Tallinn"], idx["Bucharest"]}

    # Directed adjacency set (allowing direct flights)
    allowed = set()
    def add_undirected(a, b):
        allowed.add((idx[a], idx[b]))
        allowed.add((idx[b], idx[a]))
    def add_direct(a, b):
        allowed.add((idx[a], idx[b]))

    # Add routes
    add_undirected("London", "Hamburg")
    add_undirected("London", "Reykjavik")
    add_undirected("Milan", "Barcelona")
    add_undirected("Reykjavik", "Barcelona")
    add_direct("Reykjavik", "Stuttgart")  # directed
    add_undirected("Stockholm", "Reykjavik")
    add_undirected("London", "Stuttgart")
    add_undirected("Milan", "Zurich")
    add_undirected("London", "Barcelona")
    add_undirected("Stockholm", "Hamburg")
    add_undirected("Zurich", "Barcelona")
    add_undirected("Stockholm", "Stuttgart")
    add_undirected("Milan", "Hamburg")
    add_undirected("Stockholm", "Tallinn")
    add_undirected("Hamburg", "Bucharest")
    add_undirected("London", "Bucharest")
    add_undirected("Milan", "Stockholm")
    add_undirected("Stuttgart", "Hamburg")
    add_undirected("London", "Zurich")
    add_undirected("Milan", "Reykjavik")
    add_undirected("London", "Stockholm")
    add_undirected("Milan", "Stuttgart")
    add_undirected("Stockholm", "Barcelona")
    add_undirected("London", "Milan")
    add_undirected("Zurich", "Hamburg")
    add_undirected("Bucharest", "Barcelona")
    add_undirected("Zurich", "Stockholm")
    add_undirected("Barcelona", "Tallinn")
    add_undirected("Zurich", "Tallinn")
    add_undirected("Hamburg", "Barcelona")
    add_undirected("Stuttgart", "Barcelona")
    add_undirected("Zurich", "Reykjavik")
    add_undirected("Zurich", "Bucharest")

    # Targets for desired days in each city
    target_days = {
        "Zurich": 2,
        "Bucharest": 2,
        "Hamburg": 5,
        "Barcelona": 4,
        "Reykjavik": 5,
        "Stuttgart": 5,
        "Stockholm": 2,
        "Tallinn": 4,
        "Milan": 5,
        "London": 3
    }
    targets = [0]*len(cities)
    for name, t in target_days.items():
        targets[idx[name]] = t

    days = list(range(1, 29))  # 1..28

    # Decision variables: City at end of each day
    City = {d: Int(f"City_{d}") for d in days}

    o = Optimize()
    o.set(priority='lex')

    # Domain constraints
    for d in days:
        o.add(And(City[d] >= 0, City[d] < len(cities)))

    # Hard schedule for fixed windows (enforce being in specific cities as primary end-of-day city)
    # Construct fixed base plan for days 1..12:
    # Day 1-2 London, Day 3-6 Milan, Day 7-8 Zurich, Day 9-12 Reykjavik
    o.add(City[1] == idx["London"])
    o.add(City[2] == idx["London"])
    o.add(City[3] == idx["Milan"])
    o.add(City[4] == idx["Milan"])
    o.add(City[5] == idx["Milan"])
    o.add(City[6] == idx["Milan"])
    o.add(City[7] == idx["Zurich"])
    o.add(City[8] == idx["Zurich"])
    o.add(City[9] == idx["Reykjavik"])
    o.add(City[10] == idx["Reykjavik"])
    o.add(City[11] == idx["Reykjavik"])
    o.add(City[12] == idx["Reykjavik"])

    # From day 13 to 28, remain within set B (the remaining 6 cities)
    for d in range(13, 29):
        o.add(Or([City[d] == b for b in B_set]))

    # Adjacency (flight) constraints across days (for any change, must be allowed direct flight)
    for d in range(2, 29):
        change = City[d] != City[d-1]
        allowed_pairs = Or([And(City[d-1] == a, City[d] == b) for (a, b) in allowed]) if allowed else False
        o.add(Implies(change, allowed_pairs))

    # "In city on day" indicators and totals
    def in_city_expr(c, d):
        if d == 1:
            return City[1] == c
        else:
            # In city c on day d if c is the end-of-day city, or we departed from c on day d
            return Or(City[d] == c, And(City[d] != City[d-1], City[d-1] == c))

    totals = []
    for c in range(len(cities)):
        tot = Sum([If(in_city_expr(c, d), 1, 0) for d in days])
        totals.append(tot)

    # Hard inclusion windows (must attend/meet/visit on specified days)
    # London days 1-3 (annual show)
    for d in [1, 2, 3]:
        o.add(in_city_expr(idx["London"], d))
    # Milan days 3-7 (friends)
    for d in [3, 4, 5, 6, 7]:
        o.add(in_city_expr(idx["Milan"], d))
    # Zurich days 7-8 (conference)
    for d in [7, 8]:
        o.add(in_city_expr(idx["Zurich"], d))
    # Reykjavik days 9-13 (relatives)
    for d in [9, 10, 11, 12, 13]:
        o.add(in_city_expr(idx["Reykjavik"], d))

    # Ensure we visit all 10 cities (at least 1 day in each)
    for c in range(len(cities)):
        o.add(totals[c] >= 1)

    # Objective 1: minimize total deviation from desired days in each city
    abs_devs = []
    for c in range(len(cities)):
        t = targets[c]
        abs_dev = If(totals[c] >= t, totals[c] - t, t - totals[c])
        abs_devs.append(abs_dev)
    o.minimize(Sum(abs_devs))

    # Objective 2: minimize number of flight days (changes)
    changes = Sum([If(City[d] != City[d-1], 1, 0) for d in range(2, 29)])
    o.minimize(changes)

    # Solve
    if o.check() != sat:
        # Fallback: return empty itinerary if unsat (should not happen with soft constraints)
        print(json.dumps({"itinerary": []}))
        return

    m = o.model()
    city_vals = {d: m[City[d]].as_long() for d in days}

    # Build compressed itinerary segments based on end-of-day city
    itinerary = []
    start_day = 1
    current_city = city_vals[1]
    for d in range(2, 29):
        if city_vals[d] != current_city:
            itinerary.append({
                "day_range": f"Day {start_day}-{d-1}",
                "place": cities[current_city]
            })
            start_day = d
            current_city = city_vals[d]
    itinerary.append({
        "day_range": f"Day {start_day}-28",
        "place": cities[current_city]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
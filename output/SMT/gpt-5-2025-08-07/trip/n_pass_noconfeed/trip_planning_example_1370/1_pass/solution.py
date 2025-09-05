import json
from z3 import *

def main():
    # Define cities and durations (days in each city)
    cities = ["Santorini", "Krakow", "Paris", "Vilnius", "Munich", "Geneva", "Amsterdam", "Budapest", "Split"]
    city_index = {name: i for i, name in enumerate(cities)}
    durations = [5, 5, 5, 3, 5, 2, 4, 5, 4]  # aligned with the 'cities' list

    n = len(cities)

    # Build directed flight graph (edges)
    edges = set()

    def add_bidir(a, b):
        ia, ib = city_index[a], city_index[b]
        edges.add((ia, ib))
        edges.add((ib, ia))

    def add_dir(a, b):
        ia, ib = city_index[a], city_index[b]
        edges.add((ia, ib))

    # Add edges as specified
    add_bidir("Paris", "Krakow")
    add_bidir("Paris", "Amsterdam")
    add_bidir("Paris", "Split")
    add_dir("Vilnius", "Munich")
    add_bidir("Paris", "Geneva")
    add_bidir("Amsterdam", "Geneva")
    add_bidir("Munich", "Split")
    add_bidir("Split", "Krakow")
    add_bidir("Munich", "Amsterdam")
    add_bidir("Budapest", "Amsterdam")
    add_bidir("Split", "Geneva")
    add_bidir("Vilnius", "Split")
    add_bidir("Munich", "Geneva")
    add_bidir("Munich", "Krakow")
    add_dir("Krakow", "Vilnius")
    add_bidir("Vilnius", "Amsterdam")
    add_bidir("Budapest", "Paris")
    add_bidir("Krakow", "Amsterdam")
    add_bidir("Vilnius", "Paris")
    add_bidir("Budapest", "Geneva")
    add_bidir("Split", "Amsterdam")
    add_bidir("Santorini", "Geneva")
    add_bidir("Amsterdam", "Santorini")
    add_bidir("Munich", "Budapest")
    add_bidir("Munich", "Paris")

    # SMT variables
    order = [Int(f"order_{i}") for i in range(n)]  # permutation of cities
    start = [Int(f"start_{i}") for i in range(n)]  # start day (inclusive) of city at position i
    end = [Int(f"end_{i}") for i in range(n)]      # end day (inclusive) of city at position i

    s = Solver()

    # Each order[i] is a valid city index
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    s.add(Distinct(order))  # visit each city exactly once

    # Helper to get duration of the city placed at position i
    def dur_expr(i):
        return Sum([If(order[i] == k, durations[k], 0) for k in range(n)])

    # Timeline constraints with overlap flights:
    # - start_0 = 1
    # - end_i = start_i + duration(order[i]) - 1
    # - start_{i+1} = end_i (one-day overlap counted in both cities)
    # - end_{n-1} = 30
    s.add(start[0] == 1)
    for i in range(n):
        s.add(end[i] == start[i] + dur_expr(i) - 1)
        s.add(start[i] >= 1, start[i] <= 30)
        s.add(end[i] >= 1, end[i] <= 30)
        s.add(end[i] >= start[i])  # positive duration
        if i > 0:
            s.add(start[i] == end[i - 1])
    s.add(end[n - 1] == 30)

    # Direct flight constraints between consecutive cities
    allowed_pairs = list(edges)
    for i in range(n - 1):
        s.add(Or([And(order[i] == src, order[i + 1] == dst) for (src, dst) in allowed_pairs]))

    # Time window constraints:
    # Paris: meet a friend between day 11 and day 15
    # Krakow: wedding between day 18 and day 22
    # Santorini: meet friends between day 25 and day 29
    def window_constraint(city_name, L, R):
        cid = city_index[city_name]
        return Or([And(order[i] == cid, start[i] <= R, end[i] >= L) for i in range(n)])

    s.add(window_constraint("Paris", 11, 15))
    s.add(window_constraint("Krakow", 18, 22))
    s.add(window_constraint("Santorini", 25, 29))

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    m = s.model()

    # Extract solution
    itinerary = []
    for i in range(n):
        ci = m.eval(order[i]).as_long()
        st = m.eval(start[i]).as_long()
        en = m.eval(end[i]).as_long()
        itinerary.append({
            "day_range": f"Day {st}-{en}",
            "place": cities[ci]
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
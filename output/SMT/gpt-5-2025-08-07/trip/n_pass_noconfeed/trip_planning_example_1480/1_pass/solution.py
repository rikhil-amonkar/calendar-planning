import json
from z3 import *

def main():
    # Define cities and mapping
    cities = [
        "Istanbul", "Vienna", "Riga", "Brussels", "Madrid",
        "Vilnius", "Venice", "Geneva", "Munich", "Reykjavik"
    ]
    city_index = {name: i for i, name in enumerate(cities)}
    n_cities = len(cities)
    total_days = 27

    # Durations per city
    durations = {
        "Istanbul": 4,
        "Vienna": 4,
        "Riga": 2,
        "Brussels": 2,
        "Madrid": 4,
        "Vilnius": 4,
        "Venice": 5,
        "Geneva": 4,
        "Munich": 5,
        "Reykjavik": 2
    }

    # Build directed flight edges: "A and B" => both directions; "from A to B" => A->B only
    edges = set()
    def add_bidir(a, b):
        edges.add((city_index[a], city_index[b]))
        edges.add((city_index[b], city_index[a]))
    def add_dir(a, b):
        edges.add((city_index[a], city_index[b]))

    add_bidir("Munich", "Vienna")
    add_bidir("Istanbul", "Brussels")
    add_bidir("Vienna", "Vilnius")
    add_bidir("Madrid", "Munich")
    add_bidir("Venice", "Brussels")
    add_bidir("Riga", "Brussels")
    add_bidir("Geneva", "Istanbul")
    add_bidir("Munich", "Reykjavik")
    add_bidir("Vienna", "Istanbul")
    add_bidir("Riga", "Istanbul")
    add_bidir("Reykjavik", "Vienna")
    add_bidir("Venice", "Munich")
    add_bidir("Madrid", "Venice")
    add_bidir("Vilnius", "Istanbul")
    add_bidir("Venice", "Vienna")
    add_bidir("Venice", "Istanbul")
    add_dir("Reykjavik", "Madrid")
    add_dir("Riga", "Munich")
    add_bidir("Munich", "Istanbul")
    add_bidir("Reykjavik", "Brussels")
    add_bidir("Vilnius", "Brussels")
    add_dir("Vilnius", "Munich")
    add_bidir("Madrid", "Vienna")
    add_bidir("Vienna", "Riga")
    add_bidir("Geneva", "Vienna")
    add_bidir("Madrid", "Brussels")
    add_bidir("Vienna", "Brussels")
    add_bidir("Geneva", "Brussels")
    add_bidir("Geneva", "Madrid")
    add_bidir("Munich", "Brussels")
    add_bidir("Madrid", "Istanbul")
    add_bidir("Geneva", "Munich")
    add_dir("Riga", "Vilnius")

    # SMT variables for a 10-segment chain covering 27 days (with overlap on transition days)
    k = n_cities  # 10 segments, each a unique city
    city_vars = [Int(f"city_{i}") for i in range(k)]
    start_vars = [Int(f"start_{i}") for i in range(k)]
    end_vars = [Int(f"end_{i}") for i in range(k)]

    s = Solver()

    # Domain constraints
    for i in range(k):
        s.add(And(city_vars[i] >= 0, city_vars[i] < n_cities))
        s.add(And(start_vars[i] >= 1, start_vars[i] <= total_days))
        s.add(And(end_vars[i] >= 1, end_vars[i] <= total_days))
        s.add(end_vars[i] >= start_vars[i])

    # All cities must be visited exactly once (permutation)
    s.add(Distinct(*city_vars))

    # Timeline coverage: start overall at day 1 and end at day 27
    s.add(start_vars[0] == 1)
    s.add(end_vars[k - 1] == total_days)

    # Overlap on transition days: flying on day X means being in both cities on day X
    for i in range(k - 1):
        s.add(end_vars[i] == start_vars[i + 1])

    # Duration constraints tied to selected city
    for i in range(k):
        # end - start + 1 == duration(city[i])
        dur_expr = Sum([If(city_vars[i] == city_index[name], durations[name], 0) for name in cities])
        s.add(end_vars[i] - start_vars[i] + 1 == dur_expr)

    # Build helper expressions to get start/end for a specific city (since each appears exactly once)
    def start_of(city_name):
        idx = city_index[city_name]
        return Sum([If(city_vars[i] == idx, start_vars[i], 0) for i in range(k)])
    def end_of(city_name):
        idx = city_index[city_name]
        return Sum([If(city_vars[i] == idx, end_vars[i], 0) for i in range(k)])

    # Window constraints:
    # - Brussels wedding between day 26 and 27 => must be in Brussels on both days 26 and 27
    #   With duration 2, this effectively fixes Brussels to 26-27
    s.add(start_of("Brussels") <= 26)
    s.add(end_of("Brussels") >= 27)

    # - Venice workshop between day 7 and day 11 => Venice must intersect [7, 11]
    s.add(start_of("Venice") <= 11)
    s.add(end_of("Venice") >= 7)

    # - Geneva relatives between day 1 and day 4 => Geneva must intersect [1, 4]
    s.add(start_of("Geneva") <= 4)
    s.add(end_of("Geneva") >= 1)

    # - Vilnius friends between day 20 and day 23 => Vilnius must intersect [20, 23]
    s.add(start_of("Vilnius") <= 23)
    s.add(end_of("Vilnius") >= 20)

    # Direct flight constraints between consecutive cities (directed)
    for i in range(k - 1):
        s.add(Or([And(city_vars[i] == u, city_vars[i + 1] == v) for (u, v) in edges]))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found under given constraints.")
    m = s.model()

    # Extract itinerary in order of segments
    itinerary = []
    for i in range(k):
        c_idx = m.eval(city_vars[i]).as_long()
        start_day = m.eval(start_vars[i]).as_long()
        end_day = m.eval(end_vars[i]).as_long()
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": cities[c_idx]
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
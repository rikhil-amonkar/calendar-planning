# Requires: z3-solver
# pip install z3-solver

from z3 import *
import json

def main():
    # Cities and indices
    cities = [
        "Oslo",
        "Helsinki",
        "Edinburgh",
        "Riga",
        "Tallinn",
        "Budapest",
        "Vilnius",
        "Porto",
        "Geneva",
    ]
    idx = {c: i for i, c in enumerate(cities)}

    # Durations (days counted with overlap rule)
    required_days = {
        "Oslo": 2,
        "Helsinki": 2,
        "Edinburgh": 3,
        "Riga": 2,
        "Tallinn": 5,
        "Budapest": 5,
        "Vilnius": 5,
        "Porto": 5,
        "Geneva": 4,
    }

    # Build directed adjacency set according to the statement
    allowed = set()

    def add_bidir(a, b):
        allowed.add((idx[a], idx[b]))
        allowed.add((idx[b], idx[a]))

    def add_dir(a, b):
        allowed.add((idx[a], idx[b]))

    # Given direct flights
    add_bidir("Porto", "Oslo")
    add_bidir("Edinburgh", "Budapest")
    add_bidir("Edinburgh", "Geneva")
    add_dir("Riga", "Tallinn")
    add_bidir("Edinburgh", "Porto")
    add_bidir("Vilnius", "Helsinki")
    add_dir("Tallinn", "Vilnius")
    add_bidir("Riga", "Oslo")
    add_bidir("Geneva", "Oslo")
    add_bidir("Edinburgh", "Oslo")
    add_bidir("Edinburgh", "Helsinki")
    add_bidir("Vilnius", "Oslo")
    add_bidir("Riga", "Helsinki")
    add_bidir("Budapest", "Geneva")
    add_bidir("Helsinki", "Budapest")
    add_bidir("Helsinki", "Oslo")
    add_bidir("Edinburgh", "Riga")
    add_bidir("Tallinn", "Helsinki")
    add_bidir("Geneva", "Porto")
    add_bidir("Budapest", "Oslo")
    add_bidir("Helsinki", "Geneva")
    add_dir("Riga", "Vilnius")
    add_bidir("Tallinn", "Oslo")

    # Z3 setup
    s = Solver()

    # 25 days, one city per day (0..8)
    n_days = 25
    C = [Int(f"day_{d+1}") for d in range(n_days)]
    for d in range(n_days):
        s.add(And(C[d] >= 0, C[d] < len(cities)))

    # Direct-flight constraint: if city changes from day d to d+1, it must be an allowed directed edge
    for d in range(n_days - 1):
        same = C[d] == C[d + 1]
        # Or over all allowed (i,j)
        moves = Or([And(C[d] == i, C[d + 1] == j) for (i, j) in allowed]) if allowed else False
        s.add(Or(same, moves))

    # Count days per city with overlap rule:
    # count_k = sum_{d=1..25} [C[d]==k] + sum_{d=2..25} [C[d-1]==k and C[d-1]!=C[d]]
    def iverson(b):
        return If(b, 1, 0)

    for city, req in required_days.items():
        k = idx[city]
        present_days = Sum([iverson(C[d] == k) for d in range(n_days)])
        depart_overlap = Sum([iverson(And(C[d - 1] == k, C[d - 1] != C[d])) for d in range(1, n_days)])
        s.add(present_days + depart_overlap == req)

    # Wedding in Tallinn between day 4 and day 8 inclusive:
    # "In city on day d" means: C[d]==city OR (d>1 and C[d-1]==city and C[d-1]!=C[d])
    def in_city_on_day(k, d):  # d is 0-based index
        if d == 0:
            return C[d] == k
        return Or(C[d] == k, And(C[d - 1] == k, C[d - 1] != C[d]))

    tallinn = idx["Tallinn"]
    wedding_days = [in_city_on_day(tallinn, d) for d in range(3, 8)]  # days 4..8 -> indices 3..7
    s.add(Or(wedding_days))

    # Meet friend in Oslo between day 24 and day 25 inclusive
    oslo = idx["Oslo"]
    meet_days = [in_city_on_day(oslo, 23), in_city_on_day(oslo, 24)]  # days 24,25 -> idx 23,24
    s.add(Or(meet_days))

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": [], "status": "UNSAT"}))
        return

    m = s.model()
    itinerary = []
    for d in range(n_days):
        city_name = cities[m[C[d]].as_long()]
        itinerary.append({"day": d + 1, "place": city_name})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()
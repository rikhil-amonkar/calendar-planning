# Solve the 25-day, 10-city itinerary with flight-day double counting using Z3
# and output a JSON-formatted itinerary.
#
# IMPORTANT: If you fly from city A to city B on day X, day X counts for BOTH A and B.
#
# The program enforces:
# - Exact required day counts per city (including double-count on flight days)
# - Time window presence constraints (being in a city counts if either you are there that day, or you depart from it that day)
# - Only direct flights are used when changing cities between consecutive days
# - Outputs JSON with a list of day->city mappings (no separate flight entries)
from z3 import *
import json

def main():
    # Cities and indices
    cities = [
        "Paris", "Warsaw", "Krakow", "Tallinn", "Riga",
        "Copenhagen", "Helsinki", "Oslo", "Santorini", "Lyon"
    ]
    idx = {c: i for i, c in enumerate(cities)}

    # Required exact days in each city
    required_days = {
        "Paris": 5,
        "Warsaw": 2,
        "Krakow": 2,
        "Tallinn": 2,
        "Riga": 2,
        "Copenhagen": 5,
        "Helsinki": 5,
        "Oslo": 5,
        "Santorini": 2,
        "Lyon": 4,
    }

    # Directed flight graph: "A and B" => add both directions; "from A to B" => only A->B
    directed_edges = set()

    def add_bidirectional(a, b):
        directed_edges.add((idx[a], idx[b]))
        directed_edges.add((idx[b], idx[a]))

    def add_direct(a, b):
        directed_edges.add((idx[a], idx[b]))

    # Add edges from the prompt
    add_bidirectional("Warsaw", "Riga")
    add_bidirectional("Warsaw", "Tallinn")
    add_bidirectional("Copenhagen", "Helsinki")
    add_bidirectional("Lyon", "Paris")
    add_bidirectional("Copenhagen", "Warsaw")
    add_bidirectional("Lyon", "Oslo")
    add_bidirectional("Paris", "Oslo")
    add_bidirectional("Paris", "Riga")
    add_bidirectional("Krakow", "Helsinki")
    add_bidirectional("Paris", "Tallinn")
    add_bidirectional("Oslo", "Riga")
    add_bidirectional("Krakow", "Warsaw")
    add_bidirectional("Paris", "Helsinki")
    add_bidirectional("Copenhagen", "Santorini")
    add_bidirectional("Helsinki", "Warsaw")
    add_bidirectional("Helsinki", "Riga")
    add_bidirectional("Copenhagen", "Krakow")
    add_bidirectional("Copenhagen", "Riga")
    add_bidirectional("Paris", "Krakow")
    add_bidirectional("Copenhagen", "Oslo")
    add_bidirectional("Oslo", "Tallinn")
    add_bidirectional("Oslo", "Helsinki")
    add_bidirectional("Copenhagen", "Tallinn")
    add_bidirectional("Oslo", "Krakow")
    add_direct("Riga", "Tallinn")
    add_bidirectional("Helsinki", "Tallinn")
    add_bidirectional("Paris", "Copenhagen")
    add_bidirectional("Paris", "Warsaw")
    add_direct("Santorini", "Oslo")
    add_bidirectional("Oslo", "Warsaw")

    days = 25
    # Variables: City on each day (destination/stay city for that day)
    City = [Int(f"City_{d}") for d in range(1, days + 1)]

    s = Solver()

    # Domain constraints
    for d in range(days):
        s.add(And(City[d] >= 0, City[d] < len(cities)))

    # Movement constraints: if city changes from day d-1 to d, it must be a direct flight
    for d in range(1, days):
        s.add(Or(
            City[d] == City[d - 1],
            Or([And(City[d - 1] == a, City[d] == b) for (a, b) in directed_edges])
        ))

    # Presence predicate: In city c on day d if City[d]==c (being/arriving/staying),
    # or if d>1 and City[d-1]==c and City[d]!=City[d-1] (departing from c on day d)
    def in_city_on_day(c_idx, d):  # d is 0-based here
        if d == 0:
            return City[0] == c_idx
        return Or(
            City[d] == c_idx,
            And(City[d - 1] == c_idx, City[d] != City[d - 1])
        )

    # Exact day counts per city
    for cname, req in required_days.items():
        c = idx[cname]
        s.add(Sum([If(in_city_on_day(c, d), 1, 0) for d in range(days)]) == req)

    # Time window constraints:
    # - Paris friend meet between day 4 and day 8 (1-based)
    paris_idx = idx["Paris"]
    s.add(Or([in_city_on_day(paris_idx, d - 1) for d in range(4, 9)]))

    # - Krakow workshop on days 17 and 18 (must be present both days)
    krk_idx = idx["Krakow"]
    s.add(in_city_on_day(krk_idx, 16))  # day 17
    s.add(in_city_on_day(krk_idx, 17))  # day 18

    # - Riga wedding on days 23 and 24 (must be present both days)
    riga_idx = idx["Riga"]
    s.add(in_city_on_day(riga_idx, 22))  # day 23
    s.add(in_city_on_day(riga_idx, 23))  # day 24

    # - Santorini relatives on days 12 and 13 (must be present both days)
    sant_idx = idx["Santorini"]
    s.add(in_city_on_day(sant_idx, 11))  # day 12
    s.add(in_city_on_day(sant_idx, 12))  # day 13

    # - Helsinki friend meet between day 18 and day 22 (present at least one day)
    hel_idx = idx["Helsinki"]
    s.add(Or([in_city_on_day(hel_idx, d - 1) for d in range(18, 23)]))

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    m = s.model()

    # Build itinerary
    itinerary = []
    for d in range(days):
        city_name = cities[m[City[d]].as_long()]
        itinerary.append({"day": d + 1, "city": city_name})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
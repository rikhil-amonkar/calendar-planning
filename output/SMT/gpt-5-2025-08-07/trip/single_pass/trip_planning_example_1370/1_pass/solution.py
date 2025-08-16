import json
from z3 import *

def solve_itinerary():
    # Cities and indices
    cities = [
        "Santorini",
        "Krakow",
        "Paris",
        "Vilnius",
        "Munich",
        "Geneva",
        "Amsterdam",
        "Budapest",
        "Split",
    ]
    n_cities = len(cities)
    city_index = {name: i for i, name in enumerate(cities)}

    # Required days per city (with flight-day counting rule)
    required_days = {
        "Santorini": 5,
        "Krakow": 5,
        "Paris": 5,
        "Vilnius": 3,
        "Munich": 5,
        "Geneva": 2,
        "Amsterdam": 4,
        "Budapest": 5,
        "Split": 4,
    }

    # Build allowed directed flight pairs (including staying in the same city)
    allowed_pairs = set()
    # Staying put is always allowed
    for c in range(n_cities):
        allowed_pairs.add((c, c))

    def add_bidir(a, b):
        ua = city_index[a]; vb = city_index[b]
        allowed_pairs.add((ua, vb))
        allowed_pairs.add((vb, ua))

    def add_dir(a, b):
        ua = city_index[a]; vb = city_index[b]
        allowed_pairs.add((ua, vb))

    # Given flight connectivity:
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

    # Decision variables: city for each day 1..30 (0-based index for array)
    days = 30
    city = [Int(f"city_{d+1}") for d in range(days)]

    s = Solver()

    # Domains
    for d in range(days):
        s.add(And(city[d] >= 0, city[d] < n_cities))

    # Movement constraints: either stay or take an allowed direct flight
    for d in range(1, days):
        s.add(Or([And(city[d-1] == u, city[d] == v) for (u, v) in allowed_pairs]))

    # Flight counting: number of changes (flights) should be 8
    # Because total required-days sum is 38; 30 calendar days + 8 flight overlaps = 38
    flights = Sum([If(city[d] != city[d-1], 1, 0) for d in range(1, days)])
    s.add(flights == 8)

    # Presence function: on day d (1-based), you are present in current city,
    # and also present in previous city if a flight occurs on day d.
    def present_on_day(c_idx, d1_based):
        d = d1_based - 1
        if d == 0:
            return city[0] == c_idx
        else:
            return Or(
                city[d] == c_idx,
                And(city[d-1] == c_idx, city[d] != city[d-1])
            )

    # Required total days per city (including flight-day overlaps)
    for name, req in required_days.items():
        c = city_index[name]
        # days assigned to city itself
        assigned = Sum([If(city[d] == c, 1, 0) for d in range(days)])
        # days counted due to departing from this city (flight day counts for both)
        overlaps = Sum([If(And(city[d-1] == c, city[d] != city[d-1]), 1, 0) for d in range(1, days)])
        s.add(assigned + overlaps == req)

    # Meeting windows:
    # Paris between day 11 and 15
    paris = city_index["Paris"]
    s.add(Or([present_on_day(paris, d) for d in range(11, 16)]))
    # Krakow between day 18 and 22
    krakow = city_index["Krakow"]
    s.add(Or([present_on_day(krakow, d) for d in range(18, 23)]))
    # Santorini between day 25 and 29
    santorini = city_index["Santorini"]
    s.add(Or([present_on_day(santorini, d) for d in range(25, 30)]))

    # Optionally, fix last day to Santorini (feasible and helps solver converge)
    s.add(city[days - 1] == santorini)

    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found under given constraints.")

    m = s.model()
    itinerary = []
    for d in range(days):
        c_idx = m[city[d]].as_long()
        itinerary.append({"day": d + 1, "city": cities[c_idx]})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    solve_itinerary()
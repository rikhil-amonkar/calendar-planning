# Requires: z3-solver
# pip install z3-solver

from z3 import *
import json

def solve_itinerary():
    # Cities indexed
    cities = [
        "Rome",       # 0
        "Mykonos",    # 1
        "Nice",       # 2
        "Munich",     # 3
        "Riga",       # 4
        "Bucharest",  # 5
        "Krakow"      # 6
    ]
    city_index = {name: i for i, name in enumerate(cities)}

    # Required total counted days per city
    required = {
        "Mykonos": 3,
        "Riga": 3,
        "Munich": 4,
        "Bucharest": 4,
        "Rome": 4,
        "Nice": 3,
        "Krakow": 2
    }
    req = [0]*len(cities)
    for name, cnt in required.items():
        req[city_index[name]] = cnt

    # Allowed direct flights (directed pairs)
    allowed = set()
    def add_bidirectional(a, b):
        allowed.add((city_index[a], city_index[b]))
        allowed.add((city_index[b], city_index[a]))
    def add_one_way(a, b):
        allowed.add((city_index[a], city_index[b]))

    add_bidirectional("Nice", "Riga")
    add_bidirectional("Bucharest", "Munich")
    add_bidirectional("Mykonos", "Munich")
    add_bidirectional("Riga", "Bucharest")
    add_bidirectional("Rome", "Nice")
    add_bidirectional("Rome", "Munich")
    add_bidirectional("Mykonos", "Nice")
    add_bidirectional("Rome", "Mykonos")
    add_bidirectional("Munich", "Krakow")
    add_bidirectional("Rome", "Bucharest")
    add_bidirectional("Nice", "Munich")
    add_one_way("Riga", "Munich")
    add_one_way("Rome", "Riga")

    DAYS = 17
    # Z3 variables: for each day d, dep[d] (where we depart from on day d), arr[d] (where we are for that day)
    dep = [Int(f"dep_{d}") for d in range(1, DAYS+1)]
    arr = [Int(f"arr_{d}") for d in range(1, DAYS+1)]

    s = Solver()

    # Domain constraints
    for d in range(DAYS):
        s.add(And(dep[d] >= 0, dep[d] < len(cities)))
        s.add(And(arr[d] >= 0, arr[d] < len(cities)))

    # Continuity: for d>=2, you depart from where you arrived the previous day
    for d in range(1, DAYS):  # 0-based indexing; day index d means calendar day d+1
        s.add(dep[d] == arr[d-1])
    # Day 1 can have no flight or a flight; dep[0] is free within domain.

    # Flight constraints: if dep != arr then (dep,arr) must be an allowed direct flight
    def allowed_flight_constraint(dep_var, arr_var):
        # Or(dep==arr, Or_{(i,j) in allowed} (dep==i and arr==j))
        pairs = []
        for (i, j) in allowed:
            pairs.append(And(dep_var == i, arr_var == j))
        return Or(dep_var == arr_var, Or(*pairs)) if pairs else dep_var == arr_var

    for d in range(DAYS):
        s.add(allowed_flight_constraint(dep[d], arr[d]))

    # Count days for each city:
    # For each day:
    # - Arrival city (arr[d]) always contributes 1 day to that city.
    # - If there is a flight (dep[d] != arr[d]), then the departure city also gets +1 day.
    counts = [Int(f"count_{c}") for c in range(len(cities))]
    for c in range(len(cities)):
        day_contribs = []
        for d in range(DAYS):
            # 1 if arr[d] == c else 0
            arr_contrib = If(arr[d] == c, 1, 0)
            # 1 if dep[d] == c and dep[d] != arr[d] else 0
            dep_extra = If(And(dep[d] == c, dep[d] != arr[d]), 1, 0)
            day_contribs.append(arr_contrib + dep_extra)
        s.add(counts[c] == Sum(day_contribs))

    # Match required totals per city
    for c in range(len(cities)):
        s.add(counts[c] == req[c])

    # Must attend conference in Rome on day 1 and day 4
    # Being in a city on day d holds if arr[d-1]==city (as departure city dep[d]) or arr[d]==city.
    day1 = 1
    day4 = 4
    rome = city_index["Rome"]
    s.add(Or(arr[day1-1] == rome, dep[day1-1] == rome))  # Day 1
    s.add(Or(arr[day4-1] == rome, dep[day4-1] == rome))  # Day 4

    # Wedding in Mykonos between day 4 and day 6 (inclusive): must be in Mykonos on at least one of these days
    myk = city_index["Mykonos"]
    presence_myk = []
    for d in range(4, 7):
        presence_myk.append(Or(arr[d-1] == myk, dep[d-1] == myk))
    s.add(Or(*presence_myk))

    # Annual show in Krakow from day 16 to day 17: be in Krakow both days
    krk = city_index["Krakow"]
    for d in [16, 17]:
        s.add(Or(arr[d-1] == krk, dep[d-1] == krk))
    # To make the itinerary clearer, force being stationed (arr) in Krakow on days 16 and 17
    s.add(arr[16-1] == krk)
    s.add(arr[17-1] == krk)

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": []}, indent=2))
        return

    m = s.model()
    itinerary = []
    for d in range(1, DAYS+1):
        city_name = cities[m[arr[d-1]].as_long()]
        itinerary.append({"day": d, "city": city_name})

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    solve_itinerary()
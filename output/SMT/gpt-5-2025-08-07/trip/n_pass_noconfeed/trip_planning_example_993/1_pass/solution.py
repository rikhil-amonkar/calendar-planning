import json
from z3 import *

def main():
    # Problem parameters
    days_total = 15
    cities = ["Riga", "Frankfurt", "Amsterdam", "Vilnius", "London", "Stockholm", "Bucharest"]
    city_idx = {c: i for i, c in enumerate(cities)}
    # Desired days in each city
    desired_days = {
        "Riga": 2,
        "Frankfurt": 3,
        "Amsterdam": 2,
        "Vilnius": 5,
        "London": 2,
        "Stockholm": 3,
        "Bucharest": 4
    }

    # Direct flights (directed for 'from', undirected for 'and')
    edges = set()
    def add_and(a, b):
        edges.add((city_idx[a], city_idx[b]))
        edges.add((city_idx[b], city_idx[a]))
    def add_from(a, b):
        edges.add((city_idx[a], city_idx[b]))

    add_and("London", "Amsterdam")
    add_and("Vilnius", "Frankfurt")
    add_from("Riga", "Vilnius")
    add_and("Riga", "Stockholm")
    add_and("London", "Bucharest")
    add_and("Amsterdam", "Stockholm")
    add_and("Amsterdam", "Frankfurt")
    add_and("Frankfurt", "Stockholm")
    add_and("Bucharest", "Riga")
    add_and("Amsterdam", "Riga")
    add_and("Amsterdam", "Bucharest")
    add_and("Riga", "Frankfurt")
    add_and("Bucharest", "Frankfurt")
    add_and("London", "Frankfurt")
    add_and("London", "Stockholm")
    add_and("Amsterdam", "Vilnius")

    # SMT variables
    # s[d] = start city at day d (morning)
    # e[d] = end city at day d (evening). If a flight occurs on day d, s[d] != e[d].
    s = [Int(f"s_{d}") for d in range(1, days_total + 1)]
    e = [Int(f"e_{d}") for d in range(1, days_total + 1)]

    solver = Solver()

    # Domains
    for d in range(days_total):
        solver.add(And(s[d] >= 0, s[d] < len(cities)))
        solver.add(And(e[d] >= 0, e[d] < len(cities)))

    # Continuity: next day's start equals previous day's end
    for d in range(days_total - 1):
        solver.add(s[d + 1] == e[d])

    # Direct flight or stay constraint
    def direct_or_stay(sd, ed):
        return Or(
            ed == sd,
            Or([And(sd == a, ed == b) for (a, b) in edges])
        )
    for d in range(days_total):
        solver.add(direct_or_stay(s[d], e[d]))

    # Presence boolean: present_in[d][c] = present in city c on day d
    present_in = [[Bool(f"pres_d{d+1}_{cities[c]}") for c in range(len(cities))] for d in range(days_total)]
    for d in range(days_total):
        for c in range(len(cities)):
            solver.add(present_in[d][c] == Or(s[d] == c, e[d] == c))

    # City day counts equal desired
    for cname, cnt in desired_days.items():
        c = city_idx[cname]
        solver.add(Sum([If(present_in[d][c], 1, 0) for d in range(days_total)]) == cnt)

    # The total extra presence over 15 days equals number of flight days
    # Sum over all cities of their days = 21, hence the number of flight days must be 6.
    flight_day = [Bool(f"flight_d{d+1}") for d in range(days_total)]
    for d in range(days_total):
        solver.add(flight_day[d] == (s[d] != e[d]))
    solver.add(Sum([If(flight_day[d], 1, 0) for d in range(days_total)]) == sum(desired_days.values()) - days_total)

    # Time window constraints:
    # - Meet friend in Amsterdam between day 2 and day 3 (inclusive)
    solver.add(Or(present_in[1][city_idx["Amsterdam"]], present_in[2][city_idx["Amsterdam"]]))
    # - Workshop in Vilnius between day 7 and day 11 (inclusive): present at least one of these days
    solver.add(Or([present_in[d][city_idx["Vilnius"]] for d in range(6, 11)]))
    # - Wedding in Stockholm between day 13 and day 15 (inclusive): present at least one of these days
    solver.add(Or([present_in[d][city_idx["Stockholm"]] for d in range(12, 15)]))

    # Solve
    if solver.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return
    model = solver.model()

    # Extract solution
    s_val = [model.evaluate(s[d]).as_long() for d in range(days_total)]
    e_val = [model.evaluate(e[d]).as_long() for d in range(days_total)]

    # Build human-readable itinerary entries per day
    itinerary = []
    for d in range(days_total):
        sd = cities[s_val[d]]
        ed = cities[e_val[d]]
        if s_val[d] == e_val[d]:
            place = sd
        else:
            place = f"{sd} -> {ed}"
        itinerary.append({"day_range": f"Day {d+1}", "place": place})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()
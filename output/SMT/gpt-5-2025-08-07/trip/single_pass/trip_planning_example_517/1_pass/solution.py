import json
from z3 import *

def solve_itinerary():
    # Problem setup
    N_DAYS = 19
    cities = ["Bucharest", "Warsaw", "Stuttgart", "Copenhagen", "Dubrovnik"]
    idx = {name: i for i, name in enumerate(cities)}

    # Direct flight edges (bidirectional)
    edges = set()
    def add_edge(a, b):
        edges.add((idx[a], idx[b]))
        edges.add((idx[b], idx[a]))

    add_edge("Warsaw", "Copenhagen")
    add_edge("Stuttgart", "Copenhagen")
    add_edge("Warsaw", "Stuttgart")
    add_edge("Bucharest", "Copenhagen")
    add_edge("Bucharest", "Warsaw")
    add_edge("Copenhagen", "Dubrovnik")

    # Desired days per city under the "flight day counts for both cities" rule
    desired = {
        "Dubrovnik": 5,
        "Warsaw": 2,
        "Stuttgart": 7,
        "Bucharest": 6,
        "Copenhagen": 3
    }

    # Z3 variables
    # city[d] is the main listed city for day d (0-based index for days)
    city = [Int(f"city_{d+1}") for d in range(N_DAYS)]
    s = Solver()

    # Domain constraints
    for d in range(N_DAYS):
        s.add(And(city[d] >= 0, city[d] < len(cities)))

    # Flight transitions and adjacency constraints
    # If city changes from day d to day d+1, there must be a direct flight
    transitions = []
    for d in range(N_DAYS - 1):
        flight_pairs = [And(city[d] == a, city[d + 1] == b) for (a, b) in edges]
        s.add(Or(city[d] == city[d + 1], Or(flight_pairs)))
        transitions.append(If(city[d] != city[d + 1], 1, 0))
    transitions_count = Sum(transitions)
    # Based on totals: sum(desired) = 23 = 19 + number_of_flights => number_of_flights must be 4
    s.add(transitions_count == 4)

    # Count days per city under the counting rule:
    # total_days(C) = assigned_days(C) + inbound_flights_into_C
    for name in cities:
        c = idx[name]
        assigned = Sum([If(city[d] == c, 1, 0) for d in range(N_DAYS)])
        inbound = Sum([If(And(city[d] != city[d + 1], city[d + 1] == c), 1, 0) for d in range(N_DAYS - 1)])
        s.add(assigned + inbound == desired[name])

    # Conference in Stuttgart on day 7 and day 13:
    # Presence on a day X holds if city[X]==Stuttgart OR inbound flight to Stuttgart on day X (i.e., city[X+1]==Stuttgart)
    STG = idx["Stuttgart"]
    # Day indices: day 7 -> index 6, day 13 -> index 12
    s.add(Or(city[6] == STG, city[7] == STG))   # Day 7 presence
    s.add(Or(city[12] == STG, city[13] == STG)) # Day 13 presence

    # Wedding in Bucharest between day 1 and day 6 (inclusive)
    # Presence on day d in [1..6]: city[d]==Bucharest OR inbound into Bucharest that day (city[d+1]==Bucharest)
    BUC = idx["Bucharest"]
    wedding_presence = []
    for d in range(6):  # indices 0..5 correspond to days 1..6
        cond = Or(city[d] == BUC, city[d + 1] == BUC)
        wedding_presence.append(cond)
    s.add(Or(wedding_presence))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found.")
    m = s.model()

    itinerary = []
    for d in range(N_DAYS):
        itinerary.append({
            "day": d + 1,
            "city": cities[m.eval(city[d]).as_long()]
        })

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    solve_itinerary()
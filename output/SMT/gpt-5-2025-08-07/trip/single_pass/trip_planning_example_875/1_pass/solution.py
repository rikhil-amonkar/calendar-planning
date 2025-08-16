import json
from z3 import *

def solve_itinerary():
    # Days
    D = 20
    days = list(range(1, D + 1))

    # City indices
    STU, EDI, ATH, SPL, KRK, VCE, MYK = 0, 1, 2, 3, 4, 5, 6
    city_names = ["Stuttgart", "Edinburgh", "Athens", "Split", "Krakow", "Venice", "Mykonos"]

    # Required total counted days per city (including flight-day overlap)
    required_days = {
        STU: 3,
        EDI: 4,
        ATH: 4,
        SPL: 2,
        KRK: 4,
        VCE: 5,
        MYK: 4
    }

    # Direct flight edges (undirected)
    edges = set()
    def add_edge(a, b):
        edges.add((a, b))
        edges.add((b, a))

    add_edge(KRK, SPL)
    add_edge(SPL, ATH)
    add_edge(EDI, KRK)
    add_edge(VCE, STU)
    add_edge(KRK, STU)
    add_edge(EDI, STU)
    add_edge(STU, ATH)
    add_edge(VCE, EDI)
    add_edge(ATH, MYK)
    add_edge(VCE, ATH)
    add_edge(STU, SPL)
    add_edge(EDI, ATH)

    # Z3 variables: city per day (base city of the day)
    city = {d: Int(f"city_{d}") for d in days}

    s = Solver()

    # Domain constraints
    for d in days:
        s.add(And(city[d] >= 0, city[d] <= 6))

    # Flight adjacency constraints: if city changes between d and d+1, it must be a direct flight
    for d in range(1, D):
        # Either same city (no flight), or a valid direct flight (adjacent)
        allowed_transitions = [And(city[d] == a, city[d+1] == b) for (a, b) in edges]
        s.add(Or(city[d] == city[d+1], Or(allowed_transitions)))

    # Count presence per city per day with flight-day overlap:
    # A city c is "present" on day d if:
    # - base city on day d: city[d] == c
    # - OR if there is a change between day d and d+1 and the destination on day d+1 is c
    #   (i.e., the flight happens on day d and counts for both origin and destination)
    present = {}
    for c in range(7):
        present[c] = []
        for d in days:
            if d < D:
                present_d = If(Or(city[d] == c, And(city[d] != city[d+1], city[d+1] == c)), 1, 0)
            else:
                # On day D, only base city counts (no flight after day D)
                present_d = If(city[d] == c, 1, 0)
            present[c].append(present_d)

    # Duration constraints
    for c in range(7):
        s.add(Sum(present[c]) == required_days[c])

    # Exactly 6 changes (because sum of required days across cities = 26 = 20 + number_of_changes)
    changes = [If(city[d] != city[d+1], 1, 0) for d in range(1, D)]
    s.add(Sum(changes) == 6)

    # Time window constraints (presence includes flight-day overlap)
    # - Stuttgart workshop between day 11 and day 13: present at least one of those days
    s.add(Sum([present[STU][d-1] for d in range(11, 14)]) >= 1)

    # - Meet friends in Split between day 13 and day 14: present at least one of those days
    s.add(Sum([present[SPL][d-1] for d in range(13, 15)]) >= 1)

    # - Meet friend in Krakow between day 8 and day 11: present at least one of those days
    s.add(Sum([present[KRK][d-1] for d in range(8, 12)]) >= 1)

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found.")

    m = s.model()

    itinerary = []
    for d in days:
        c_idx = m.eval(city[d]).as_long()
        itinerary.append({"day": d, "city": city_names[c_idx]})

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    solve_itinerary()
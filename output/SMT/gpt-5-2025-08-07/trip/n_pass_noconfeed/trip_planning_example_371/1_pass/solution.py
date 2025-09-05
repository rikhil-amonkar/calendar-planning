import json
from z3 import Solver, Int, Or, And, If, Sum, sat

def main():
    # Parameters
    days = 9
    city_names = ["Vienna", "Stockholm", "Nice", "Split"]
    VIE, STO, NCE, SPL = 0, 1, 2, 3

    # Required presence days per city
    required_days = {
        VIE: 2,
        STO: 5,
        NCE: 2,
        SPL: 3,
    }

    # Direct flight pairs (undirected)
    direct_pairs = set()
    def add_pair(a, b):
        direct_pairs.add((a, b))
        direct_pairs.add((b, a))

    add_pair(VIE, STO)
    add_pair(VIE, NCE)
    add_pair(VIE, SPL)
    add_pair(STO, SPL)
    add_pair(NCE, STO)

    # Z3 variables: city[d] is the city at the end of day d (1-indexed)
    city = {d: Int(f"city_{d}") for d in range(1, days + 1)}

    s = Solver()

    # Domain constraints: city[d] in {0,1,2,3}
    for d in range(1, days + 1):
        s.add(Or(city[d] == VIE, city[d] == STO, city[d] == NCE, city[d] == SPL))

    # Flight adjacency and counting: at most one flight per day implicitly (between end-of-day cities)
    flight_bools = []
    for d in range(2, days + 1):
        change = city[d] != city[d - 1]
        flight_bools.append(change)
        # If change, it must be a direct flight
        s.add(
            Or(
                city[d] == city[d - 1],
                Or(*[And(city[d - 1] == a, city[d] == b) for (a, b) in direct_pairs])
            )
        )

    # Presence function: presence of city c on day d
    def presence_expr(d, c):
        if d == 1:
            return city[1] == c
        else:
            # On flight day d, you are in both city[d-1] (if changed) and city[d]
            return Or(city[d] == c, And(city[d - 1] == c, city[d] != city[d - 1]))

    # City-day presence counts
    for c in [VIE, STO, NCE, SPL]:
        pres_sum = Sum([If(presence_expr(d, c), 1, 0) for d in range(1, days + 1)])
        s.add(pres_sum == required_days[c])

    # Workshop in Vienna between day 1 and day 2: present in Vienna on day 1 and day 2
    s.add(presence_expr(1, VIE))
    s.add(presence_expr(2, VIE))

    # Conference in Split on day 7 and day 9: present in Split on those days
    s.add(presence_expr(7, SPL))
    s.add(presence_expr(9, SPL))

    # The total number of flights must align with total city-day counts:
    # Sum of required days = 12. Total presence = 9 + flights => flights = 3
    flights_count = Sum([If(fb, 1, 0) for fb in flight_bools])
    s.add(flights_count == 3)

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found given the constraints."}))
        return

    m = s.model()

    # Extract end-of-day cities
    end_cities = [m.evaluate(city[d]).as_long() for d in range(1, days + 1)]

    # Build itinerary as contiguous ranges of identical end-of-day cities
    itinerary = []
    start = 1
    current = end_cities[0]
    for d in range(2, days + 1):
        if end_cities[d - 1] != current:
            itinerary.append({
                "day_range": f"Day {start}-{d-1}",
                "place": city_names[current]
            })
            start = d
            current = end_cities[d - 1]
    # Append last segment
    itinerary.append({
        "day_range": f"Day {start}-{days}",
        "place": city_names[current]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()